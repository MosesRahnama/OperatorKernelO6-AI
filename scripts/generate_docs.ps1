# Set project root
$ProjectRoot = "c:\Users\Moses\math_ops\OperatorKernelO6"
$OutputDir = "$ProjectRoot\docs"

# Create output directory
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir -Force
}

Write-Host "Generating documentation for OperatorKernelO6..." -ForegroundColor Green

# Method 1: Using Pandoc (recommended)
if (Get-Command pandoc -ErrorAction SilentlyContinue) {
    Write-Host "Using Pandoc..." -ForegroundColor Yellow
    
    # Create a combined markdown file
    $CombinedMd = "$OutputDir\OperatorKernelO6_Complete.md"
    
    # Header
    @"
# OperatorKernelO6: Ordinal-Based Termination Analysis

**Author:** Moses  
**Date:** $(Get-Date -Format 'yyyy-MM-dd')  
**Project:** Operator Kernel O6 - Meta-level termination proofs using ordinal measures

---

## Abstract

This document presents a formalization in Lean 4 of termination proofs for trace reduction systems using ordinal-based measures. The core contribution is a systematic approach to proving strong normalization through carefully constructed ordinal functions μ : Trace → Ordinal.

---

"@ | Out-File -FilePath $CombinedMd -Encoding UTF8

    # Process each Lean file
    Get-ChildItem -Path "$ProjectRoot\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
        $RelativePath = $_.FullName.Replace("$ProjectRoot\", "")
        $FileContent = Get-Content $_.FullName -Raw
        
        @"
## $RelativePath

``````lean4
$FileContent
``````

---

"@ | Out-File -FilePath $CombinedMd -Append -Encoding UTF8
    }
    
    # Convert to PDF with nice formatting
    $PdfOutput = "$OutputDir\OperatorKernelO6_Documentation.pdf"
    
    pandoc $CombinedMd -o $PdfOutput `
        --pdf-engine=xelatex `
        --highlight-style=tango `
        --variable geometry:margin=1in `
        --variable fontsize=11pt `
        --variable documentclass=article `
        --variable colorlinks=true `
        --variable linkcolor=blue `
        --variable urlcolor=blue `
        --variable toccolor=gray `
        --toc `
        --toc-depth=3
        
    Write-Host "PDF generated: $PdfOutput" -ForegroundColor Green
    
} else {
    Write-Host "Pandoc not found. Would you like to install it?" -ForegroundColor Yellow
    Write-Host "1. Install Pandoc automatically (requires admin)" -ForegroundColor White
    Write-Host "2. Skip PDF, create HTML only" -ForegroundColor White
    Write-Host "3. Exit and install manually" -ForegroundColor White
    
    $choice = Read-Host "Enter choice (1-3)"
    
    switch ($choice) {
        "1" {
            Write-Host "Installing Pandoc via winget..." -ForegroundColor Yellow
            winget install --id=JohnMacFarlane.Pandoc -e
            Write-Host "Please restart PowerShell and run this script again." -ForegroundColor Red
            exit
        }
        "2" {
            Write-Host "Proceeding with HTML only..." -ForegroundColor Yellow
        }
        default {
            Write-Host "Exiting. Please install Pandoc manually from: https://pandoc.org/installing.html" -ForegroundColor Yellow
            exit
        }
    }
}

# Method 2: Simple HTML version (always works)
Write-Host "Generating HTML version..." -ForegroundColor Yellow

$HtmlOutput = "$OutputDir\OperatorKernelO6_Documentation.html"

@"
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>OperatorKernelO6 Documentation</title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github.min.css">
    <script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script>
    <style>
        body { font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; margin: 40px; line-height: 1.6; }
        h1 { color: #2c3e50; border-bottom: 3px solid #3498db; }
        h2 { color: #34495e; border-bottom: 1px solid #bdc3c7; }
        pre { background: #f8f9fa; padding: 15px; border-radius: 5px; overflow-x: auto; }
        code { background: #f1f2f6; padding: 2px 4px; border-radius: 3px; }
        .file-header { background: #e8f4fd; padding: 10px; margin: 20px 0; border-left: 4px solid #3498db; }
    </style>
</head>
<body>
    <h1>OperatorKernelO6: Ordinal-Based Termination Analysis</h1>
    <p><strong>Author:</strong> Moses<br>
    <strong>Date:</strong> $(Get-Date -Format 'yyyy-MM-dd')<br>
    <strong>Project:</strong> Operator Kernel O6 - Meta-level termination proofs</p>
    
    <h2>Abstract</h2>
    <p>This document presents a formalization in Lean 4 of termination proofs for trace reduction systems using ordinal-based measures. The core contribution is a systematic approach to proving strong normalization through carefully constructed ordinal functions μ : Trace → Ordinal.</p>
"@ | Out-File -FilePath $HtmlOutput -Encoding UTF8

Get-ChildItem -Path "$ProjectRoot\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
    $RelativePath = $_.FullName.Replace("$ProjectRoot\", "")
    $FileContent = Get-Content $_.FullName -Raw
    $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($FileContent)
    
    @"
    <div class="file-header">
        <h2>$RelativePath</h2>
    </div>
    <pre><code class="language-lean">$EscapedContent</code></pre>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8
}

@"
    <script>hljs.highlightAll();</script>
</body>
</html>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8

Write-Host "HTML generated: $HtmlOutput" -ForegroundColor Green
Write-Host "You can open this in Chrome and print to PDF!" -ForegroundColor Cyan

# Method 3: Create README.md for GitHub
$ReadmePath = "$ProjectRoot\README.md"
@"
# OperatorKernelO6: Ordinal-Based Termination Analysis

A Lean 4 formalization of termination proofs for trace reduction systems using ordinal measures.

## Structure

- `OperatorKernelO6/Kernel.lean` - Core trace definitions and reduction rules
- `OperatorKernelO6/Meta/TerminationBase.lean` - Ordinal measure μ and basic lemmas  
- `OperatorKernelO6/Meta/Termination.lean` - Main termination theorem

## Key Results

- **μ-measure decrease**: Every reduction step `a → b` satisfies `μ(b) < μ(a)`
- **Strong normalization**: The reduction relation is well-founded
- **Ordinal bounds**: Concrete ordinal arithmetic for each trace constructor

## Documentation

Run `.\scripts\generate_docs.ps1` to generate PDF/HTML documentation.
"@ | Out-File -FilePath $ReadmePath -Encoding UTF8

Write-Host "README.md created: $ReadmePath" -ForegroundColor Green
Write-Host "`nDocumentation generation complete!" -ForegroundColor Green
