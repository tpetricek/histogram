#load "packages/FsLab/FsLab.fsx"
open Deedle
open XPlot.GoogleCharts

System.Environment.CurrentDirectory <- __SOURCE_DIRECTORY__

// Try to load data from one file by hand
let ap1 = Frame.ReadCsv("raw/avia_paoc.tsv",separators="\t",missingValues=[|":"|])
let keys = Seq.head(ap1.ColumnKeys).Split(',') |> Seq.map (fun k -> if k = "geo\\time" then "geo" else k)
let ap2 = ap1.GetColumnAt<string>(0) |> Series.map (fun _ v -> series (Seq.zip keys (v.Split(',')))) |> Frame.ofRows
let ap' = ap1 |> Frame.dropCol (Seq.head(ap1.ColumnKeys)) |> Frame.merge ap2

// Extract a reusable function for doing this
let readEurostatFile (file:string) = 
  let f1 = Frame.ReadCsv(file,separators="\t",missingValues=[|":"; ": z"; ": c"|])
  let keys = Seq.head(f1.ColumnKeys).Split(',') |> Seq.map (fun k -> if k = "geo\\time" then "geo" else k)
  let f2 = f1.GetColumnAt<string>(0) |> Series.map (fun _ v -> series (Seq.zip keys (v.Split(',')))) |> Frame.ofRows
  f1 |> Frame.dropCol (Seq.head(f1.ColumnKeys)) |> Frame.merge f2

// Call it to load two files and do some post-hoc fiddling
let ap = 
  readEurostatFile "raw/avia_paoc.tsv"
  |> Frame.filterRows (fun _ row -> 
    row.GetAs("tra_meas") = "CAF_PAS" && row.GetAs("schedule") = "TOT" && row.GetAs("tra_cov") = "TOTAL"
      && row.GetAs("geo") <> "EU27" && row.GetAs("geo") <> "EU28")
  |> Frame.indexRowsString "geo"

let tp = 
  readEurostatFile "raw/rail_pa_total.tsv" 
  |> Frame.filterRows (fun _ row -> 
    row.GetAs("unit") = "THS_PAS" && row.GetAs("geo") <> "EU27" && row.GetAs("geo") <> "EU28")
  |> Frame.indexRowsString "geo"

// Some calculation to get values per year, only for countries with sensible data
let tp17 = tp?``2017``
let ap17 = ap?``2017Q1`` + ap?``2017Q2`` + ap?``2017Q3`` + ap?``2017Q4``
let large = 
  frame [ "Train" => tp17; "Air" => ap17 ]
  |> Frame.filterRows (fun _ row -> row?Train > 1000.0)

// Data visualization - total passengers and ratio of train to air
Chart.Column(large)
log (large?Air / large?Train) |> Chart.Column



