param(
    [string]$CacheRoot
)

$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $auditFile = 'JH/Audit.lean'
    $requiredFiles = @($auditFile, 'JH/Graph/Walk.lean', 'JH/Model.lean', 'JH/Probability/UniformPMF.lean',
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
    $requiredFiles += Get-ChildItem -LiteralPath 'JH' -Filter '*Spec.lean' -File -Recurse |
        ForEach-Object { $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\', '/') }
    $registeredFiles = @()
    foreach ($entry in Get-Content -LiteralPath 'statements.sha256') {
        if ($entry -cnotmatch '^([a-f0-9]{64})  (JH/[A-Za-z0-9/]+\.lean|lean-toolchain|lakefile\.toml|lake-manifest\.json)$') {
            throw "Invalid frozen statement entry: $entry"
        }
        $expectedHash = $Matches[1]
        $path = $Matches[2]
        $registeredFiles += $path
        $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
        if ($actualHash -cne $expectedHash) {
            throw "Frozen definitions or statements have changed: $path"
        }
    }
    if (Compare-Object -CaseSensitive $requiredFiles $registeredFiles) {
        throw 'The statement manifest must cover every specification, the audit and toolchain files.'
    }

    $lakeOptions = @()
    if ($CacheRoot) {
        # Proxy packages expose only compiled imports. Lake writes under this project.
        $lock = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
        $overrides = @()
        # Keep the canonical Lean options and library targets when replacing dependencies.
        $sections = (Get-Content -LiteralPath 'lakefile.toml' -Raw) -split '(?m)(?=^\[)'
        $projectConfig = ($sections | Where-Object { $_ -cnotmatch '^\[\[require\]\]' }) -join ''
        $config = @(
            '# Generated for this cache by verify.ps1.',
            'buildDir = ".cached-dependencies/.lake/build"',
            $projectConfig.TrimEnd()
        )
        foreach ($dependency in $lock.packages) {
            $packageRoot = Join-Path $CacheRoot $dependency.name
            $libraryPath = Join-Path $packageRoot '.lake/build/lib/lean'
            if ($dependency.name -eq 'Cli' -and
                -not (Test-Path -LiteralPath $libraryPath -PathType Container)) {
                continue
            }
            $cacheRevision = (Get-Content -Raw -LiteralPath "$packageRoot/.git/HEAD").Trim()
            if ($cacheRevision.StartsWith('ref: ')) {
                $ref = $cacheRevision.Substring(5)
                $cacheRevision = (Get-Content -Raw -LiteralPath "$packageRoot/.git/$ref").Trim()
            }
            if ($cacheRevision -cne $dependency.rev) {
                throw "Cached package revision does not match the lock file: $($dependency.name)"
            }
            $libraryPath = (Resolve-Path -LiteralPath $libraryPath).Path.Replace('\', '/')
            $packageName = 'cached_' + $dependency.name.ToLowerInvariant()
            $proxyRoot = ".cached-dependencies/$packageName"
            New-Item -ItemType Directory -Path $proxyRoot -Force | Out-Null
            $proxyConfig = @("name = ""$packageName""", "leanLibDir = ""$libraryPath""")
            [IO.File]::WriteAllLines("$PSScriptRoot/$proxyRoot/lakefile.toml", $proxyConfig)
            $overrides += @{
                name = $packageName
                type = 'path'
                dir = $proxyRoot
                configFile = 'lakefile.toml'
                inherited = $false
            }
            $config += @('', '[[require]]', "name = ""$packageName""", "path = ""$proxyRoot""")
        }
        [IO.File]::WriteAllLines("$PSScriptRoot/lakefile.offline.toml", $config)
        $overrideJson = @{ version = $lock.version; packages = $overrides } | ConvertTo-Json -Depth 4
        [IO.File]::WriteAllText("$PSScriptRoot/lake-manifest.offline.json", $overrideJson)
        $lakeOptions = @('-f', 'lakefile.offline.toml', '--packages=lake-manifest.offline.json')
    }

    & lake @lakeOptions --wfail build
    if ($LASTEXITCODE -ne 0) {
        throw 'Lake build failed.'
    }

    $allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
    $output = & lake @lakeOptions lean $auditFile
    if ($LASTEXITCODE -ne 0) {
        $output | Write-Output
        throw "Lean audit failed: $auditFile"
    }
    $output | Write-Output
    $auditText = $output -join [Environment]::NewLine
    $reports = [regex]::Matches($auditText,
        "(?m)^'.+' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])")
    $expectedReports = @(Select-String -LiteralPath $auditFile -Pattern '^#print axioms ').Count
    if ($expectedReports -eq 0 -or $reports.Count -ne $expectedReports) {
        throw "Incomplete axiom reports: $auditFile"
    }
    foreach ($report in $reports) {
        if ($report.Groups[1].Success) {
            foreach ($dependency in $report.Groups[1].Value.Split(',')) {
                if ($dependency.Trim() -cnotin $allowedAxioms) {
                    throw "Unexpected axiom: $($dependency.Trim())"
                }
            }
        }
    }
    Write-Output 'Statement hashes, Lean build and audited axiom dependencies passed.'
}
finally {
    Pop-Location
}
