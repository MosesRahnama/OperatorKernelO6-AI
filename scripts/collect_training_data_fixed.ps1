# OperatorKernelO6 AI Training Data Collection
Write-Host "🔥 COLLECTING TRAINING DATA FOR OPERATORKERNELO6 AI 🔥" -ForegroundColor Red
Write-Host "Creating a personalized AI mathematician..." -ForegroundColor Yellow

# Create training directory structure
New-Item -ItemType Directory -Force -Path "ai_training_data\raw_data"
New-Item -ItemType Directory -Force -Path "ai_training_data\processed_data" 
New-Item -ItemType Directory -Force -Path "ai_training_data\datasets"

Write-Host "📚 Collecting Lean source code..." -ForegroundColor Green

# Collect all Lean files
$leanOutput = "ai_training_data\raw_data\lean_code.txt"
"" | Out-File $leanOutput
Get-ChildItem -Recurse -Filter "*.lean" | ForEach-Object {
    Write-Host "Processing: $($_.FullName)"
    "=== LEAN SOURCE: $($_.Name) ===" | Add-Content $leanOutput
    Get-Content $_.FullName | Add-Content $leanOutput
    "`n`n" | Add-Content $leanOutput
}

Write-Host "📖 Collecting documentation..." -ForegroundColor Green

# Collect all markdown files
$docOutput = "ai_training_data\raw_data\documentation.txt"
"" | Out-File $docOutput
Get-ChildItem -Recurse -Filter "*.md" | ForEach-Object {
    Write-Host "Processing: $($_.FullName)"
    "=== DOCUMENTATION: $($_.Name) ===" | Add-Content $docOutput
    Get-Content $_.FullName | Add-Content $docOutput
    "`n`n" | Add-Content $docOutput
}

Write-Host "📋 Collecting mathematical frameworks..." -ForegroundColor Green

# Collect specific high-value files
$mathOutput = "ai_training_data\raw_data\mathematical_frameworks.txt"
"" | Out-File $mathOutput

$highValueFiles = @(
    "core_docs\agent.md",
    "core_docs\ordinal-toolkit.md", 
    "OperatorKernelO6\Meta\Termination_Companion.md",
    "copilot-instructions.md",
    "copilot-instructions_large.md"
)

foreach ($file in $highValueFiles) {
    if (Test-Path $file) {
        Write-Host "Processing high-value: $file"
        "=== MATHEMATICAL FRAMEWORK: $file ===" | Add-Content $mathOutput
        Get-Content $file | Add-Content $mathOutput
        "`n`n" | Add-Content $mathOutput
    }
}

Write-Host "🔧 Collecting configuration files..." -ForegroundColor Green

# Collect config files
$configOutput = "ai_training_data\raw_data\config.txt"
"" | Out-File $configOutput
Get-ChildItem -Recurse -Include "lakefile.lean","*.json","lean-toolchain" | ForEach-Object {
    Write-Host "Processing: $($_.FullName)"
    "=== CONFIG: $($_.Name) ===" | Add-Content $configOutput
    Get-Content $_.FullName | Add-Content $configOutput
    "`n`n" | Add-Content $configOutput
}

Write-Host "✅ Data collection complete!" -ForegroundColor Green
Write-Host "📊 Training data saved in ai_training_data\" -ForegroundColor Cyan
Write-Host "🧠 Ready to create your personal AI mathematician!" -ForegroundColor Magenta
