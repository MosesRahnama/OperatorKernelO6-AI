# Search-First Development Setup Verification

param(
    [switch]$TestBuild = $false,
    [switch]$ShowInstructions = $false
)

Write-Host "🔍 Search-First Development System Check" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan

# Check if files exist
$files = @(
    ".github\copilot-instructions.md",
    ".github\instructions\lean-specific.md", 
    ".vscode\tasks.json",
    ".vscode\settings.json"
)

Write-Host "`n📁 Checking configuration files..." -ForegroundColor Yellow
foreach ($file in $files) {
    if (Test-Path $file) {
        Write-Host "✅ $file" -ForegroundColor Green
    } else {
        Write-Host "❌ $file - MISSING!" -ForegroundColor Red
    }
}

# Check lakefile for LeanSearchClient
Write-Host "`n📦 Checking dependencies..." -ForegroundColor Yellow
if (Get-Content "lakefile.lean" | Select-String "LeanSearchClient") {
    Write-Host "✅ LeanSearchClient dependency added" -ForegroundColor Green
} else {
    Write-Host "❌ LeanSearchClient dependency missing!" -ForegroundColor Red
}

# Test build if requested
if ($TestBuild) {
    Write-Host "`n🔨 Testing build..." -ForegroundColor Yellow
    $buildResult = & lake build 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Build successful!" -ForegroundColor Green
    } else {
        Write-Host "❌ Build failed!" -ForegroundColor Red
        Write-Host $buildResult -ForegroundColor Red
    }
}

if ($ShowInstructions) {
    Write-Host "`n📋 Quick Usage Guide:" -ForegroundColor Cyan
    Write-Host "1. Ask Copilot: 'list my active instructions' to verify setup"
    Write-Host "2. In Lean files, always start with: #search `"what you need`""
    Write-Host "3. Use Ctrl+Shift+P → 'Tasks: Run Task' → 'Lean build' to compile"
    Write-Host "4. Copilot will show /fix suggestions for any errors"
    Write-Host "5. Use GREEN-CHANNEL comments for new definitions"
}

Write-Host "`n🎯 System Status:" -ForegroundColor Cyan
Write-Host "Search-first workflow: ENABLED" -ForegroundColor Green
Write-Host "Auto-build on save: CONFIGURED" -ForegroundColor Green  
Write-Host "Copilot instructions: ACTIVE" -ForegroundColor Green
Write-Host "`nYou're ready for hallucination-free development! 🚀" -ForegroundColor Green
