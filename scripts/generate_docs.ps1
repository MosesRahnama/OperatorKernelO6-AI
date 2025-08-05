# Set project root
$ProjectRoot = "c:\Users\Moses\math_ops\OperatorKernelO6"
$OutputDir = "$ProjectRoot\docs"

# Create output directory
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir -Force
}

Write-Host "Generating documentation for OperatorKernelO6..." -ForegroundColor Green

# EXTREME FULL-WIDTH HTML - Force use of entire browser width
Write-Host "Generating EXTREME full-width HTML..." -ForegroundColor Yellow

$HtmlOutput = "$OutputDir\OperatorKernelO6_Documentation.html"

Add-Type -AssemblyName System.Web

@"
<!DOCTYPE html>
<html style="width: 100vw; margin: 0; padding: 0;">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OperatorKernelO6 Documentation</title>
    <style>
        * {
            box-sizing: border-box;
        }
        html {
            width: 100vw !important;
            margin: 0 !important;
            padding: 0 !important;
        }
        body { 
            font-family: 'Times New Roman', Times, serif; 
            width: 100vw !important;     /* VIEWPORT WIDTH - FULL SCREEN */
            max-width: 100vw !important; /* FORCE VIEWPORT WIDTH */
            min-width: 100vw !important; /* MINIMUM VIEWPORT WIDTH */
            margin: 0 !important;        /* ABSOLUTELY NO MARGINS */
            padding: 10px !important;    /* TINY PADDING */
            line-height: 1.4; 
            font-size: 18pt;             /* LARGE FONT */
            color: #333;
            background: white;
            overflow-x: visible;
        }
        h1 { 
            color: #2c3e50; 
            border-bottom: 3px solid #3498db; 
            font-size: 32pt;             /* HUGE TITLE */
            margin: 0 0 15px 0 !important;
            padding-bottom: 8px;
            width: 100%;
        }
        h2 { 
            color: #34495e; 
            border-bottom: 2px solid #bdc3c7; 
            font-size: 26pt;             /* BIG HEADINGS */
            margin: 20px 0 10px 0 !important;
            padding-bottom: 5px;
            page-break-before: always;
            width: 100%;
        }
        h3 {
            font-size: 20pt;
            color: #2c3e50;
            margin: 15px 0 8px 0 !important;
            width: 100%;
        }
        pre { 
            background: #f8f9fa; 
            padding: 8px !important;     /* MINIMAL PADDING */
            border-radius: 3px; 
            overflow-x: auto; 
            font-size: 15pt !important;  /* BIG CODE FONT */
            line-height: 1.2;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            border: 1px solid #dee2e6;
            page-break-inside: avoid;
            white-space: pre-wrap;
            word-wrap: break-word;
            margin: 5px 0 !important;
            width: calc(100vw - 20px) !important; /* ALMOST FULL VIEWPORT WIDTH */
        }
        code { 
            background: #f1f2f6; 
            padding: 1px 3px; 
            border-radius: 2px; 
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            font-size: 16pt;
        }
        .file-header { 
            background: #e8f4fd; 
            padding: 8px !important;
            margin: 10px 0 5px 0 !important;
            border-left: 4px solid #3498db;
            border-radius: 3px;
            font-size: 16pt;
            width: calc(100vw - 20px) !important;
        }
        .abstract {
            background: #f0f8f0;
            padding: 8px !important;
            border-left: 4px solid #27ae60;
            margin: 10px 0 !important;
            border-radius: 3px;
            font-size: 16pt;
            width: calc(100vw - 20px) !important;
        }
        .toc {
            background: #fff3cd;
            padding: 8px !important;
            border-left: 4px solid #ffc107;
            margin: 10px 0 !important;
            border-radius: 3px;
            font-size: 16pt;
            width: calc(100vw - 20px) !important;
        }
        .toc ul {
            list-style-type: none;
            padding-left: 0;
            margin: 0 !important;
        }
        .toc li {
            margin: 3px 0 !important;
            padding-left: 10px;
        }
        .toc a {
            color: #2c3e50;
            text-decoration: none;
            font-weight: bold;
        }
        .toc a:hover {
            text-decoration: underline;
        }
        p {
            margin: 5px 0 !important;
            font-size: 18pt;
            width: 100%;
        }
        ul, ol {
            font-size: 18pt;
            line-height: 1.4;
            margin: 5px 0 !important;
            padding-left: 20px;
        }
        li {
            margin-bottom: 3px !important;
        }
        strong {
            font-weight: bold;
        }
        /* EXTREME PDF Print Optimizations */
        @media print {
            * {
                box-sizing: border-box !important;
            }
            html {
                width: 100% !important;
                margin: 0 !important;
                padding: 0 !important;
            }
            body { 
                width: 100% !important;
                max-width: 100% !important;
                margin: 0 !important;
                padding: 8px !important;
                font-size: 16pt !important;
                line-height: 1.3;
            }
            h1 {
                font-size: 28pt !important;
                margin: 0 0 12px 0 !important;
            }
            h2 {
                font-size: 22pt !important;
                margin: 15px 0 8px 0 !important;
            }
            h3 {
                font-size: 18pt !important;
                margin: 10px 0 5px 0 !important;
            }
            pre { 
                font-size: 13pt !important;
                padding: 6px !important;
                page-break-inside: avoid; 
                line-height: 1.1;
                margin: 3px 0 !important;
                width: 100% !important;
            }
            .file-header {
                page-break-after: avoid;
                font-size: 14pt !important;
                padding: 6px !important;
                margin: 8px 0 4px 0 !important;
                width: 100% !important;
            }
            .abstract, .toc {
                font-size: 14pt !important;
                padding: 6px !important;
                margin: 6px 0 !important;
                width: 100% !important;
            }
            p, ul, ol {
                font-size: 16pt !important;
                margin: 3px 0 !important;
            }
            h2 {
                page-break-before: always;
            }
            .file-header + pre {
                page-break-before: avoid;
            }
        }
        @page {
            margin: 0.3in !important;    /* TINY PAGE MARGINS */
            size: letter;
        }
    </style>
</head>
<body>
    <h1>OperatorKernelO6: Ordinal-Based Termination Analysis</h1>
    
    <div class="abstract">
        <h3>Abstract</h3>
        <p><strong>Author:</strong> Moses | <strong>Date:</strong> $(Get-Date -Format 'yyyy-MM-dd') | <strong>Project:</strong> Operator Kernel O6</p>
        
        <p>This document presents a formalization in Lean 4 of termination proofs for trace reduction systems using ordinal-based measures. The core contribution is a systematic approach to proving strong normalization through carefully constructed ordinal functions μ : Trace → Ordinal.</p>
        
        <p><strong>Key Results:</strong> μ-measure decrease (every reduction step a → b satisfies μ(b) &lt; μ(a)), strong normalization (the reduction relation is well-founded), and concrete ordinal bounds for each trace constructor.</p>
        
        <p><strong>Research Challenge:</strong> The <code>rec_succ_bound</code> lemma contains a <code>sorry</code> representing an open ordinal arithmetic problem.</p>
    </div>
    
    <div class="toc">
        <h3>Table of Contents</h3>
        <ul>
"@ | Out-File -FilePath $HtmlOutput -Encoding UTF8

# Generate TOC
$tocEntries = @()
Get-ChildItem -Path "$ProjectRoot\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
    $RelativePath = $_.FullName.Replace("$ProjectRoot\", "")
    $anchorName = $RelativePath -replace '[\\/]', '_' -replace '[^a-zA-Z0-9_]', ''
    $tocEntries += "            <li><a href=`"#$anchorName`">$RelativePath</a></li>"
}

$tocEntries -join "`n" | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8

@"
        </ul>
    </div>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8

# Process each file with EXTREME FULL WIDTH usage
Get-ChildItem -Path "$ProjectRoot\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
    $RelativePath = $_.FullName.Replace("$ProjectRoot\", "")
    $FileContent = Get-Content $_.FullName -Raw
    $EscapedContent = [System.Web.HttpUtility]::HtmlEncode($FileContent)
    $LineCount = ($FileContent -split "`n").Count
    $anchorName = $RelativePath -replace '[\\/]', '_' -replace '[^a-zA-Z0-9_]', ''
    
    $Description = switch ($_.Name) {
        "Kernel.lean" { "Core trace definitions and reduction rules" }
        "Termination.lean" { "Main termination proof with ordinal measures and mu_decreases theorem" }
        default { "Supporting definitions and lemmas" }
    }
    
    @"
    <div class="file-header" id="$anchorName">
        <h2>$RelativePath</h2>
        <p><strong>Lines:</strong> $LineCount | <strong>Description:</strong> $Description</p>
    </div>
    <pre><code>$EscapedContent</code></pre>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8
}

@"
    
    <div style="margin-top: 20px; padding: 8px; background: #fff3cd; border-left: 4px solid #ffc107; border-radius: 3px; font-size: 16pt; width: calc(100vw - 20px);">
        <h3>Converting to PDF - EXTREME INSTRUCTIONS</h3>
        <p><strong>CRITICAL STEPS:</strong></p>
        <ol>
            <li>Press <strong>Ctrl+P</strong></li>
            <li>Choose <strong>"Save as PDF"</strong></li>
            <li><strong>CRITICAL:</strong> Set Margins to <strong>"None"</strong> or <strong>"Minimum"</strong></li>
            <li><strong>CRITICAL:</strong> Set Scale to <strong>100%</strong> (NOT "Fit to page")</li>
            <li><strong>CRITICAL:</strong> Enable <strong>"Background graphics"</strong></li>
            <li><strong>CRITICAL:</strong> Make sure browser window is MAXIMIZED</li>
            <li>Click <strong>"Save"</strong></li>
        </ol>
        <p><strong>If still small:</strong> Try zooming browser to 125% or 150% BEFORE printing, then use 100% scale in print dialog.</p>
    </div>
</body>
</html>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8

Write-Host "EXTREME full-width HTML generated: $HtmlOutput" -ForegroundColor Green
Write-Host "Uses 100vw (viewport width) with minimal margins - this WILL be full width!" -ForegroundColor Cyan

# Optional: Try to use wkhtmltopdf if available
if (Get-Command wkhtmltopdf -ErrorAction SilentlyContinue) {
    Write-Host "Found wkhtmltopdf, generating PDF directly..." -ForegroundColor Yellow
    $PdfOutput = "$OutputDir\OperatorKernelO6_Documentation.pdf"
    
    wkhtmltopdf --page-size Letter --margin-top 1in --margin-bottom 1in --margin-left 1in --margin-right 1in --enable-local-file-access $HtmlOutput $PdfOutput
    
    if (Test-Path $PdfOutput) {
        Write-Host "PDF generated directly: $PdfOutput" -ForegroundColor Green
    }
} else {
    Write-Host "For automatic PDF generation, install wkhtmltopdf from: https://wkhtmltopdf.org/downloads.html" -ForegroundColor Yellow
}

# Open the HTML file
Write-Host "Opening HTML file for PDF conversion..." -ForegroundColor Cyan
Start-Process $HtmlOutput

Write-Host "`n=== INSTRUCTIONS ===" -ForegroundColor Green
Write-Host "1. The HTML file should open in your browser" -ForegroundColor White
Write-Host "2. Press Ctrl+P to print" -ForegroundColor White
Write-Host "3. Choose 'Save as PDF'" -ForegroundColor White
Write-Host "4. Set Scale to 100% (not 'Fit to page')" -ForegroundColor White
Write-Host "5. Enable 'Background graphics'" -ForegroundColor White
Write-Host "6. Use Letter size paper" -ForegroundColor White
Write-Host "`nThe fonts are now much larger and optimized for PDF!" -ForegroundColor Green
    $Description = switch ($_.Name) {
        "Kernel.lean" { "Core trace definitions and reduction rules" }
        "Termination.lean" { "Main termination proof with ordinal measures and the key mu_decreases theorem" }
        default { "Supporting definitions and lemmas" }
    }
    
    @"
    <div class="file-header" id="$anchorName">
        <h2>$RelativePath</h2>
        <p><strong>Lines:</strong> $LineCount | <strong>Description:</strong> $Description</p>
    </div>
    <pre><code class="language-lean">$EscapedContent</code></pre>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8
}

@"
    <script>hljs.highlightAll();</script>
    
    <div style="margin-top: 40px; padding: 20px; background: #fff3cd; border-left: 4px solid #ffc107; border-radius: 4px;">
        <h3>Print to PDF Instructions</h3>
        <ol>
            <li>Press <kbd>Ctrl+P</kbd> to open print dialog</li>
            <li>Choose "Save as PDF" as destination</li>
            <li>Set <strong>Paper size</strong> to "Letter" or "A4"</li>
            <li>Set <strong>Margins</strong> to "Default" or "Minimum"</li>
            <li>Enable <strong>"Background graphics"</strong> to preserve colors</li>
            <li>Set <strong>Scale</strong> to "100%" for proper font sizing</li>
        </ol>
        <p><strong>Note:</strong> The document is optimized for 12pt printing with proper page breaks.</p>
    </div>
</body>
</html>
"@ | Out-File -FilePath $HtmlOutput -Append -Encoding UTF8

Write-Host "Enhanced HTML generated: $HtmlOutput" -ForegroundColor Green
Write-Host "HTML optimized for 12pt font and proper PDF printing!" -ForegroundColor Cyan

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
