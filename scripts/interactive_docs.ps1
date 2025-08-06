param(
    [string]$OutputDir = "c:\Users\Moses\math_ops\OperatorKernelO6\docs"
)

Write-Host "=== Interactive Core Docs Combiner ===" -ForegroundColor Cyan
Write-Host ""

# Available core docs
$AvailableDocs = @(
    @{ Key = "Guide"; Name = "Complete_Guide"; Description = "Comprehensive guide to OperatorKernelO6" },
    @{ Key = "Foundations"; Name = "Operator_Centric_Foundations"; Description = "Theoretical foundations of operator-centric approach" },
    @{ Key = "Termination"; Name = "Termination_Companion"; Description = "Companion document for termination proofs" },
    @{ Key = "Agent"; Name = "Agent"; Description = "Agent-based documentation and processes" }
)

Write-Host "Available Core Documents:" -ForegroundColor Yellow
for ($i = 0; $i -lt $AvailableDocs.Count; $i++) {
    $doc = $AvailableDocs[$i]
    Write-Host "  [$($i + 1)] $($doc.Key) - $($doc.Description)" -ForegroundColor White
}

Write-Host ""
Write-Host "Enter the numbers of documents you want to combine (e.g., 1,3,4 or 1 3 4):" -ForegroundColor Green
$selection = Read-Host "Your selection"

# Parse selection
$selectedNumbers = @()
if ($selection -match ',') {
    $selectedNumbers = $selection.Split(',') | ForEach-Object { $_.Trim() }
} else {
    $selectedNumbers = $selection.Split(' ') | Where-Object { $_ -ne '' } | ForEach-Object { $_.Trim() }
}

# Convert to doc keys
$selectedDocs = @()
foreach ($num in $selectedNumbers) {
    if ($num -match '^\d+$' -and [int]$num -le $AvailableDocs.Count -and [int]$num -gt 0) {
        $selectedDocs += $AvailableDocs[[int]$num - 1].Key
    }
}

if ($selectedDocs.Count -eq 0) {
    Write-Host "No valid selections made. Exiting." -ForegroundColor Red
    exit
}

Write-Host ""
Write-Host "Selected documents (in order):" -ForegroundColor Green
foreach ($doc in $selectedDocs) {
    $docInfo = $AvailableDocs | Where-Object { $_.Key -eq $doc }
    Write-Host "  - $($docInfo.Key): $($docInfo.Description)" -ForegroundColor Gray
}

Write-Host ""
Write-Host "Do you want to reorder them? (y/n):" -ForegroundColor Yellow
$reorder = Read-Host

if ($reorder -eq 'y' -or $reorder -eq 'Y') {
    Write-Host ""
    Write-Host "Current order:" -ForegroundColor Yellow
    for ($i = 0; $i -lt $selectedDocs.Count; $i++) {
        $docInfo = $AvailableDocs | Where-Object { $_.Key -eq $selectedDocs[$i] }
        Write-Host "  [$($i + 1)] $($docInfo.Key)" -ForegroundColor White
    }
    
    Write-Host ""
    Write-Host "Enter new order (e.g., 2,1,3):" -ForegroundColor Green
    $newOrder = Read-Host "New order"
    
    $orderNumbers = $newOrder.Split(',') | ForEach-Object { $_.Trim() }
    $reorderedDocs = @()
    
    foreach ($num in $orderNumbers) {
        if ($num -match '^\d+$' -and [int]$num -le $selectedDocs.Count -and [int]$num -gt 0) {
            $reorderedDocs += $selectedDocs[[int]$num - 1]
        }
    }
    
    if ($reorderedDocs.Count -eq $selectedDocs.Count) {
        $selectedDocs = $reorderedDocs
        Write-Host ""
        Write-Host "Reordered to:" -ForegroundColor Green
        foreach ($doc in $selectedDocs) {
            $docInfo = $AvailableDocs | Where-Object { $_.Key -eq $doc }
            Write-Host "  - $($docInfo.Key)" -ForegroundColor Gray
        }
    } else {
        Write-Host "Invalid reorder. Using original order." -ForegroundColor Yellow
    }
}

Write-Host ""
Write-Host "Generating custom documentation..." -ForegroundColor Cyan

# Build the command
$coreDocsOrderString = "@('" + ($selectedDocs -join "', '") + "')"
$command = "& './scripts/convert_all_docs.ps1' -CoreDocsOrder $coreDocsOrderString -CoreDocsOnly"

Write-Host "Running: $command" -ForegroundColor Gray
Write-Host ""

# Execute the command
try {
    Invoke-Expression $command
    Write-Host ""
    Write-Host "=== Custom Documentation Created! ===" -ForegroundColor Green
    Write-Host "Check your docs folder for:" -ForegroundColor White
    Write-Host "  - Custom_Core_Documentation.html" -ForegroundColor Gray
    Write-Host "  - Custom_Core_Documentation.pdf" -ForegroundColor Gray
} catch {
    Write-Host "Error running documentation generator: $($_.Exception.Message)" -ForegroundColor Red
}

Write-Host ""
Write-Host "Press any key to exit..." -ForegroundColor Yellow
$null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")