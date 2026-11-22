use std::{fs, hint::black_box, path::PathBuf, time::Instant};
use zune_core::{bytestream::ZCursor, options::DecoderOptions};
use zune_image::{codecs::jpeg_2000::Jpeg2000Decoder, traits::DecoderTrait};

fn main() {
    let mut args = std::env::args_os().skip(1);
    let mode = args.next().unwrap();
    let dir = PathBuf::from(args.next().unwrap());
    let output = PathBuf::from(args.next().unwrap());
    fs::create_dir_all(&output).unwrap();
    let mut paths: Vec<_> = fs::read_dir(dir).unwrap().map(|p| p.unwrap().path())
        .filter(|p| matches!(p.extension().and_then(|e| e.to_str()), Some("j2k" | "jp2" | "jph" | "jpx")))
        .collect();
    paths.sort();
    println!("file\tstatus\twidth\theight\tcolor\tp50_us\tp90_us\truns");
    for path in paths {
        let name = path.file_name().unwrap().to_string_lossy();
        let input = fs::read(&path).unwrap();
        let decode = || {
            let options = DecoderOptions::default().set_strict_mode(mode != "lenient");
            Jpeg2000Decoder::new_with_options(ZCursor::new(input.as_slice()), options).decode()
        };
        let image = match std::panic::catch_unwind(decode) {
            Ok(Ok(image)) => image,
            Ok(Err(error)) => {
                println!("{name}\t{}", error.to_string().replace(['\t','\n','\r'], " "));
                continue;
            }
            Err(_) => {
                println!("{name}\tPANIC");
                continue;
            }
        };
        let (w,h) = image.dimensions();
        let color = image.colorspace();
        let frames = image.flatten_to_u8();
        fs::write(output.join(format!("{name}.bin")), &frames[0]).unwrap();
        drop(frames);
        drop(image);
        let mut times = Vec::new();
        if mode == "bench" {
            for _ in 0..3 {
                black_box(decode().unwrap());
            }
            for _ in 0..15 {
                let start = Instant::now();
                black_box(decode().unwrap());
                times.push(start.elapsed().as_secs_f64()*1e6);
            }
            times.sort_by(f64::total_cmp);
        }
        println!("{name}\tok\t{w}\t{h}\t{color:?}\t{:.2}\t{:.2}\t{}",
            times.get(7).copied().unwrap_or_default(), times.get(13).copied().unwrap_or_default(), times.len());
    }
}
