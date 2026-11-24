use jpeg2000_decoder::{
    DecodeOptions, DecodeSelection, ImageRegion, TypedImage, TypedSamples, decode_jp2,
    decode_jp2_color, decode_jp2_color_selected, decode_jp2_selected,
};
use std::io::{self, Write};

fn native(mut out: impl Write, image: &TypedImage) -> io::Result<()> {
    writeln!(
        out,
        "{} {} {} {} {}",
        image.width(),
        image.height(),
        image.x_origin(),
        image.y_origin(),
        image.components().len()
    )?;
    for comp in image.components() {
        writeln!(
            out, "{} {} {:?} {:?}", comp.width(), comp.height(), comp.info(),
            comp.channel_definitions()
        )?;
        match comp.samples() {
            TypedSamples::Unsigned(samples) => {
                for value in samples {
                    out.write_all(&value.to_le_bytes())?;
                }
            }
            TypedSamples::Signed(samples) => {
                for value in samples {
                    out.write_all(&value.to_le_bytes())?;
                }
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    let data = std::fs::read(&args[2])?;
    let discard = args[4].parse()?;
    let mut selection = DecodeSelection::full_image().with_discard_levels(discard);
    if args.len() == 9 {
        selection = selection.with_region(ImageRegion::new(
            args[5].parse()?, args[6].parse()?, args[7].parse()?, args[8].parse()?,
        ));
    }
    let selected = args.len() == 9 || discard != 0;
    let opts = DecodeOptions::default();
    let dump = args[1].ends_with("-dump");
    let loops: usize = args[3].parse()?;
    assert!(loops > 0);
    if dump {
        assert_eq!(loops, 1);
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    for _ in 0..loops {
        let input = std::hint::black_box(&data);
        if args[1].starts_with("native") {
            let image = if selected {
                decode_jp2_selected(input, &opts, &selection)?
            } else {
                decode_jp2(input, &opts)?
            };
            if dump {
                native(&mut out, &image)?;
            }
            std::hint::black_box(image);
        } else {
            let image = if selected {
                decode_jp2_color_selected(input, &opts, &selection)?
            } else {
                decode_jp2_color(input, &opts)?
            };
            if dump {
                writeln!(out, "{} {} {} {:?} {}", image.width(), image.height(), image.precision(),
                         image.color_space(), image.channels().len())?;
                for channel in image.channels() {
                    writeln!(out, "{:?}", channel.channel_type())?;
                    for sample in channel.samples() {
                        out.write_all(&sample.to_le_bytes())?;
                    }
                }
            }
            std::hint::black_box(image);
        }
    }
    Ok(())
}
