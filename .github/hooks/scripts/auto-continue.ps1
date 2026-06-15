Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Get-SessionId {
    param(
        [Parameter(Mandatory = $true)]
        [object]$Payload
    )

    if ($null -ne $Payload.PSObject.Properties['sessionId']) {
        return [string]$Payload.sessionId
    }

    if ($null -ne $Payload.PSObject.Properties['session_id']) {
        return [string]$Payload.session_id
    }

    return ''
}

function Get-Limit {
    $raw = $env:COPILOT_AUTO_CONTINUE_LIMIT
    if ([string]::IsNullOrWhiteSpace($raw)) {
        return 3
    }

    $parsed = 0
    if ([int]::TryParse($raw, [ref]$parsed) -and $parsed -ge 0) {
        return $parsed
    }

    return 3
}

function Get-StatePath {
    param(
        [Parameter(Mandatory = $true)]
        [string]$SessionId
    )

    $stateDir = Join-Path ([System.IO.Path]::GetTempPath()) 'copilot-auto-continue'
    [System.IO.Directory]::CreateDirectory($stateDir) | Out-Null
    return Join-Path $stateDir ($SessionId + '.count')
}

function Get-NextCount {
    param(
        [Parameter(Mandatory = $true)]
        [string]$StatePath
    )

    $count = 0
    if (Test-Path -LiteralPath $StatePath) {
        $existing = Get-Content -LiteralPath $StatePath -Raw
        [int]::TryParse($existing, [ref]$count) | Out-Null
    }

    $count += 1
    Set-Content -LiteralPath $StatePath -Value $count -NoNewline
    return $count
}

$rawInput = ''
if ([Console]::IsInputRedirected) {
    $rawInput = [Console]::In.ReadToEnd()
}

if ([string]::IsNullOrWhiteSpace($rawInput) -and $MyInvocation.ExpectingInput) {
    $rawInput = ($input | Out-String)
}

if ([string]::IsNullOrWhiteSpace($rawInput)) {
    exit 0
}

$payload = $rawInput | ConvertFrom-Json
$sessionId = Get-SessionId -Payload $payload
$prompt = $env:COPILOT_AUTO_CONTINUE_PROMPT

if ([string]::IsNullOrWhiteSpace($prompt)) {
    $prompt = 'Please continue improving'
}

$decision = @{ decision = 'block'; reason = $prompt }
$limit = Get-Limit

if (-not [string]::IsNullOrWhiteSpace($sessionId) -and $limit -gt 0) {
    $count = Get-NextCount -StatePath (Get-StatePath -SessionId $sessionId)
    if ($count -gt $limit) {
        $decision = @{ decision = 'allow'; reason = "Auto-continue limit $limit reached." }
    }
}

$decision | ConvertTo-Json -Compress