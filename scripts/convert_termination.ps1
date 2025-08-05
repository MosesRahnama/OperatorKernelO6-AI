param(
    [string]$InputFile = "",
    [string]$OutputDir = ""
)

# Set default paths - NOW POINTING TO THE COMBINED FILE
if ($InputFile -eq "") {
    $InputFile = "c:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6\Meta\TerminationBase.lean"
}

if ($OutputDir -eq "") {
    $OutputDir = "c:\Users\Moses\math_ops\OperatorKernelO6\docs"
}

# Create output directory
New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null

Write-Host "Converting Lean file to documentation..." -ForegroundColor Green
Write-Host "Input: $InputFile" -ForegroundColor Gray
Write-Host "Output: $OutputDir" -ForegroundColor Gray

# Check if input file exists
if (!(Test-Path $InputFile)) {
    Write-Host "ERROR: Input file not found at $InputFile" -ForegroundColor Red
    Write-Host "Available files:" -ForegroundColor Yellow
    Get-ChildItem -Path "c:\Users\Moses\math_ops\OperatorKernelO6\OperatorKernelO6" -Filter "*.lean" -Recurse | ForEach-Object {
        Write-Host "  $($_.FullName)" -ForegroundColor Gray
    }
    exit 1
}

# Read the file content with better error handling
try {
    $FileContent = Get-Content $InputFile -Raw -Encoding UTF8
    if ([string]::IsNullOrWhiteSpace($FileContent)) {
        Write-Host "WARNING: File appears to be empty" -ForegroundColor Yellow
        $FileContent = "-- File appears to be empty or could not be read properly"
    }
    Write-Host "File read successfully ($($FileContent.Length) characters)" -ForegroundColor Green
} catch {
    Write-Host "ERROR: Could not read file - $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# Generate timestamp
$Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
$DateOnly = Get-Date -Format "yyyy-MM-dd"

# Create HTML output
$HtmlFile = Join-Path $OutputDir "Termination_Documentation.html"

# Load System.Web for HTML encoding
Add-Type -AssemblyName System.Web

# Properly encode the file content for HTML
$EscapedContent = [System.Web.HttpUtility]::HtmlEncode($FileContent)

$HtmlContent = @"
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Termination Analysis - OperatorKernelO6</title>
    <style>
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            line-height: 1.6;
            color: #333;
            background: #fff;
        }
        
        h1 {
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
            margin-bottom: 30px;
        }
        
        h2 {
            color: #34495e;
            border-bottom: 1px solid #bdc3c7;
            margin-top: 40px;
            padding-bottom: 5px;
        }
        
        .metadata {
            background: #e8f4fd;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #3498db;
            margin: 20px 0;
        }
        
        .theorems {
            background: #f0f8f0;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #27ae60;
            margin: 20px 0;
        }
        
        pre {
            background: #f8f9fa;
            padding: 20px;
            border-radius: 8px;
            overflow-x: auto;
            border: 1px solid #dee2e6;
            font-size: 11px;
            line-height: 1.4;
            white-space: pre-wrap;
            word-wrap: break-word;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
        }
        
        code {
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            background: #f1f2f6;
            padding: 2px 4px;
            border-radius: 3px;
            font-size: 85%;
        }
        
        .print-instructions {
            background: #fff3cd;
            padding: 15px;
            border-radius: 8px;
            border-left: 4px solid #ffc107;
            margin-top: 40px;
        }
        
        kbd {
            background: #333;
            color: white;
            padding: 2px 6px;
            border-radius: 3px;
            font-size: 12px;
        }
        
        @media print {
            body {
                max-width: none;
                margin: 0;
                padding: 15px;
                font-size: 10px;
            }
            pre {
                font-size: 8px;
                page-break-inside: avoid;
            }
            .print-instructions {
                display: none;
            }
            h1, h2 {
                page-break-after: avoid;
            }
        }
        
        @page {
            margin: 0.75in;
        }
    </style>
</head>
<body>
    <h1>Termination Analysis - OperatorKernelO6</h1>
    
    <div class="metadata">
        <p>
            <strong>File:</strong> <code>OperatorKernelO6/Meta/TerminationBase.lean</code> (Combined)<br>
            <strong>Author:</strong> Moses<br>
            <strong>Generated:</strong> $Timestamp<br>
            <strong>File Size:</strong> $($FileContent.Length) characters
        </p>
    </div>
    
    <h2>Overview</h2>
    <p>
        This file contains the complete termination analysis for the OperatorKernelO6 system, combining both the foundational ordinal measure definitions and the main termination proof. The key result is that every reduction step decreases the ordinal measure mu, ensuring strong normalization.
    </p>
    
    <div class="theorems">
        <h3>Key Results</h3>
        <ul>
            <li><strong>Part 1 - Foundations:</strong>
                <ul>
                    <li><strong><code>mu</code></strong>: Ordinal measure mapping traces to ordinals</li>
                    <li><strong><code>termA_le</code>, <code>termB_le</code></strong>: Core inequality lemmas</li>
                    <li><strong><code>rec_succ_bound</code></strong>: Concrete bound for successor-recursor case (with sorry)</li>
                </ul>
            </li>
            <li><strong>Part 2 - Main Proof:</strong>
                <ul>
                    <li><strong><code>mu_decreases</code></strong>: Every step <code>a -&gt; b</code> satisfies <code>mu(b) &lt; mu(a)</code></li>
                    <li><strong><code>step_strong_normalization</code></strong>: The reduction relation is well-founded</li>
                    <li><strong><code>mu_lt_eq_diff</code></strong>: Inequality for equality-difference rules</li>
                </ul>
            </li>
        </ul>
    </div>
    
    <h2>Source Code</h2>
    <pre><code>$EscapedContent</code></pre>
    
    <div class="print-instructions">
        <h3>Print to PDF Instructions</h3>
        <ol>
            <li>Press <kbd>Ctrl+P</kbd> to open the print dialog</li>
            <li>Choose "Save as PDF" or "Microsoft Print to PDF"</li>
            <li>Set margins to "Minimum" or "Custom" with 0.5 inch margins</li>
            <li>Enable "Background graphics" to preserve colors</li>
            <li>Set scale to "Fit to page width" if needed</li>
        </ol>
        <p><strong>Note:</strong> The code section will automatically wrap lines for better printing.</p>
    </div>
    
    <script>
        // Simple syntax highlighting for Lean keywords
        document.addEventListener('DOMContentLoaded', function() {
            const codeElement = document.querySelector('pre code');
            if (codeElement) {
                let content = codeElement.innerHTML;
                
                // Highlight Lean keywords
                const keywords = [
                    'import', 'namespace', 'end', 'theorem', 'lemma', 'def', 'noncomputable',
                    'by', 'have', 'exact', 'simpa', 'simp', 'calc', 'cases', 'with',
                    'intro', 'apply', 'rw', 'sorry', 'private', 'open', 'universe',
                    'set_option', 'attribute'
                ];
                
                keywords.forEach(keyword => {
                    const regex = new RegExp('\\b' + keyword + '\\b', 'g');
                    content = content.replace(regex, '<span style="color: #0066cc; font-weight: bold;">' + keyword + '</span>');
                });
                
                // Highlight comments
                content = content.replace(/--[^\n]*/g, '<span style="color: #008000; font-style: italic;">$&</span>');
                
                // Highlight sorry
                content = content.replace(/\bsorry\b/g, '<span style="background: #ffcccc; color: #cc0000; font-weight: bold; padding: 1px 3px; border-radius: 2px;">sorry</span>');
                
                codeElement.innerHTML = content;
            }
        });
    </script>
</body>
</html>
"@

# Write HTML file
try {
    $HtmlContent | Out-File -FilePath $HtmlFile -Encoding UTF8
    Write-Host "SUCCESS: HTML documentation created at $HtmlFile" -ForegroundColor Green
} catch {
    Write-Host "ERROR: Could not create HTML file - $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# Try to create PDF using Pandoc (if available)
if (Get-Command pandoc -ErrorAction SilentlyContinue) {
    Write-Host "Pandoc found, attempting PDF creation..." -ForegroundColor Yellow
    
    # Create simple markdown for Pandoc
    $MarkdownFile = Join-Path $OutputDir "Termination_Documentation.md"
    
    $MarkdownContent = @"
# Termination Analysis - OperatorKernelO6

**File:** OperatorKernelO6/Meta/Termination.lean  
**Author:** Moses  
**Date:** $DateOnly

## Overview

This file contains the main termination proof for the OperatorKernelO6 system using ordinal-based measures.

## Source Code

``````lean
$FileContent
``````
"@
    
    $MarkdownContent | Out-File -FilePath $MarkdownFile -Encoding UTF8
    
    $PdfFile = Join-Path $OutputDir "Termination_Documentation.pdf"
    
    try {
        pandoc $MarkdownFile -o $PdfFile --pdf-engine=xelatex --highlight-style=tango --variable geometry:margin=0.75in --variable fontsize=11pt --standalone
        
        if (Test-Path $PdfFile) {
            Write-Host "SUCCESS: PDF created at $PdfFile" -ForegroundColor Green
            Start-Process $PdfFile
        } else {
            Write-Host "PDF creation failed (no output file)" -ForegroundColor Yellow
        }
    } catch {
        Write-Host "PDF creation failed: $($_.Exception.Message)" -ForegroundColor Yellow
    }
} else {
    Write-Host "Pandoc not found - only HTML version available" -ForegroundColor Yellow
}

# Open the HTML file