open System.Drawing
open System.Drawing.Imaging

let images = Array.init 474 (fun i -> "c:/temp/project/frame-" + (i+1).ToString().PadLeft(4,'0') + ".png")
let sample = Bitmap.FromFile(images.[0])

let n = 1

images 
|> Array.chunkBySize (n*n)
|> Array.indexed
|> Array.iter (fun (i, images) -> 
    use out = new Bitmap(sample.Width * n, sample.Height * n, PixelFormat.Format16bppRgb555)
    use gr = Graphics.FromImage(out)
    for i in 0 .. n-1 do
      for j in 0 .. n-1 do 
        if i*n+j < images.Length then
          let inp = Bitmap.FromFile(images.[i*n+j])
          gr.DrawImageUnscaled(inp, i*sample.Width, j*sample.Height) 
    
    printfn "Saving %d" i
    out.Save(@"C:\Tomas\Public\tpetricek\tbd\experiments\public\screens\gui\frame" + i.ToString().PadLeft(3, '0') + ".png", Imaging.ImageFormat.Png) 
  )

