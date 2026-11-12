#![cfg_attr(not(test), no_main)]

#[cfg(test)]
use crate::resource_limits;
use jpeg2000_decoder::{
    DecodeOptions, DecodeSelection, ImageRegion, codestream, decode_codestream,
    decode_codestream_selected, decode_jp2, decode_jp2_selected, decode_jph, decode_jph_selected,
    decode_jpx_codestream, decode_jpx_codestream_selected, inspect_jph, inspect_jpx_layers, jp2,
    render_jpx_composition, render_jpx_frame, render_jpx_layer,
};
#[cfg(not(test))]
use jpeg2000_decoder_fuzz::resource_limits;
#[cfg(not(test))]
use libfuzzer_sys::fuzz_target;

const SOC: u16 = 0xff4f;
const SIZ: u16 = 0xff51;
const COD: u16 = 0xff52;
const COC: u16 = 0xff53;
const QCD: u16 = 0xff5c;
const QCC: u16 = 0xff5d;
const RGN: u16 = 0xff5e;
const POC: u16 = 0xff5f;
const PLM: u16 = 0xff57;
const PLT: u16 = 0xff58;
const PPM: u16 = 0xff60;
const PPT: u16 = 0xff61;
const CRG: u16 = 0xff63;
const DFS: u16 = 0xff72;
const ADS: u16 = 0xff73;
const MCT: u16 = 0xff74;
const MCC: u16 = 0xff75;
const NLT: u16 = 0xff76;
const MCO: u16 = 0xff77;
const CBD: u16 = 0xff78;
const ATK: u16 = 0xff79;
const SOT: u16 = 0xff90;
const SOD: u16 = 0xff93;
const EOC: u16 = 0xffd9;

#[cfg(not(test))]
fuzz_target!(|data: &[u8]| exercise_structured_framing(data));

fn exercise_structured_framing(data: &[u8]) {
    let width = u32::from(data.first().copied().unwrap_or(0)) + 1;
    let height = u32::from(data.get(1).copied().unwrap_or(0)) + 1;
    let roi_shift = data.get(2).copied().unwrap_or(0);
    let tile_data = data.get(3..).unwrap_or_default();
    let codestream_bytes = make_codestream(
        width,
        height,
        roi_shift,
        data.get(2).copied().unwrap_or(0),
        tile_data,
    );
    let limits = resource_limits();
    assert!(codestream::parse(&codestream_bytes, &limits).is_ok());

    let palette_mapping = data.get(2).copied().unwrap_or(0) & 1 != 0;
    let jp2_bytes = make_jp2(
        &codestream_bytes,
        width,
        height,
        data.first().copied().unwrap_or(0) % 3,
        palette_mapping,
    );
    let inspected = jp2::parse_and_inspect(&jp2_bytes, &limits).unwrap();
    assert_eq!(
        inspected.file.codestream(0).unwrap().data(),
        codestream_bytes
    );
    let options = DecodeOptions::new(limits);
    let _ = decode_codestream(&codestream_bytes, &options);
    let _ = decode_jp2(&jp2_bytes, &options);
    let region =
        DecodeSelection::tile(0).with_region(ImageRegion::new(0, 0, width.max(1), height.max(1)));
    let _ = decode_codestream_selected(&codestream_bytes, &options, &region);
    let _ = decode_jp2_selected(&jp2_bytes, &options, &region);

    let ht_codestream = make_ht_codestream(width, height, data.get(2).copied().unwrap_or(0));
    let mut jph_bytes = make_jp2(&ht_codestream, width, height, 0, false);
    jph_bytes[20..24].copy_from_slice(b"jph ");
    jph_bytes[28..32].copy_from_slice(b"jph ");
    let inspected_jph = inspect_jph(&jph_bytes, &limits).unwrap();
    assert!(
        inspected_jph
            .codestream(0)
            .unwrap()
            .profile
            .uses_high_throughput()
    );
    let _ = decode_jph(&jph_bytes, &options);
    let _ = decode_jph_selected(&jph_bytes, &options, &region);

    let mut jpx_bytes = make_jp2(&codestream_bytes, width, height, 0, palette_mapping);
    jpx_bytes[20..24].copy_from_slice(b"jpxb");
    jpx_bytes[28..32].copy_from_slice(b"jpxb");
    jpx_bytes.extend(box32(*b"jp2c", &codestream_bytes));
    let inspected_jpx = jp2::parse_and_inspect(&jpx_bytes, &limits).unwrap();
    assert_eq!(inspected_jpx.codestream_count(), 2);
    let selected = usize::from(data.first().copied().unwrap_or(0) & 1);
    let _ = decode_jpx_codestream(&jpx_bytes, selected, &options);
    let _ = decode_jpx_codestream_selected(&jpx_bytes, selected, &options, &region);
    let implicit_layers = inspect_jpx_layers(&jpx_bytes, &limits).unwrap();
    assert_eq!(implicit_layers.layers().len(), 2);
    let _ = render_jpx_layer(&jpx_bytes, selected, &options);
    let _ = render_jpx_composition(&jpx_bytes, &options);
    let _ = render_jpx_frame(&jpx_bytes, 0, &options);
    let malformed =
        DecodeSelection::tiles(vec![0, 0]).with_discard_levels(data.get(3).copied().unwrap_or(0));
    let _ = decode_codestream_selected(&codestream_bytes, &options, &malformed);

    let composed = make_static_jpx(
        &codestream_bytes,
        width,
        height,
        data.get(2).copied().unwrap_or(0),
    );
    let inspected_layers = inspect_jpx_layers(&composed, &limits).unwrap();
    assert_eq!(inspected_layers.layers().len(), 1);
    let _ = render_jpx_layer(&composed, 0, &options);
    let _ = render_jpx_composition(&composed, &options);
    let _ = render_jpx_frame(&composed, 0, &options);
    let mut nested = composed;
    let mut inner = box32(*b"lbl ", b"fuzz");
    inner.extend(box32(*b"free", &[]));
    let mut outer = box32(*b"lbl ", b"outer");
    outer.extend(box32(*b"asoc", &inner));
    nested.extend(box32(*b"asoc", &outer));
    let nested_inspection = inspect_jpx_layers(&nested, &limits).unwrap();
    assert_eq!(nested_inspection.metadata_boxes(), 5);
    assert_eq!(nested_inspection.metadata_depth(), 3);
}

fn make_ht_codestream(width: u32, height: u32, selector: u8) -> Vec<u8> {
    let mut siz_payload = Vec::new();
    siz_payload.extend_from_slice(&0x4000_u16.to_be_bytes());
    siz_payload.extend_from_slice(&width.to_be_bytes());
    siz_payload.extend_from_slice(&height.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&width.to_be_bytes());
    siz_payload.extend_from_slice(&height.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&1_u16.to_be_bytes());
    siz_payload.extend_from_slice(&[7, 1, 1]);

    let style = if selector & 1 == 0 { 0x40 } else { 0xc0 };
    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(segment(SIZ, &siz_payload));
    bytes.extend(segment(0xff50, &[0, 2, 0, 0, 0, selector & 0x1f]));
    bytes.extend(segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, style, 1]));
    bytes.extend(segment(QCD, &[0, 0x40]));
    let tile_part_start = bytes.len();
    let mut sot_payload = Vec::new();
    sot_payload.extend_from_slice(&0_u16.to_be_bytes());
    sot_payload.extend_from_slice(&14_u32.to_be_bytes());
    sot_payload.extend_from_slice(&[0, 1]);
    bytes.extend(segment(SOT, &sot_payload));
    bytes.extend_from_slice(&SOD.to_be_bytes());
    assert_eq!(bytes.len() - tile_part_start, 14);
    bytes.extend_from_slice(&EOC.to_be_bytes());
    bytes
}

fn make_codestream(
    width: u32,
    height: u32,
    roi_shift: u8,
    packet_length_mode: u8,
    tile_data: &[u8],
) -> Vec<u8> {
    let mut siz_payload = Vec::new();
    siz_payload.extend_from_slice(&0_u16.to_be_bytes());
    siz_payload.extend_from_slice(&width.to_be_bytes());
    siz_payload.extend_from_slice(&height.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&width.to_be_bytes());
    siz_payload.extend_from_slice(&height.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&0_u32.to_be_bytes());
    siz_payload.extend_from_slice(&1_u16.to_be_bytes());
    siz_payload.extend_from_slice(&[7, 1, 1]);

    let mut bytes = SOC.to_be_bytes().to_vec();
    bytes.extend(segment(SIZ, &siz_payload));
    bytes.extend(segment(COD, &[0, 0, 0, 1, 0, 0, 2, 2, 0, 1]));
    bytes.extend(segment(COC, &[0, 0, 0, 1, 1, 0, 1]));
    bytes.extend(segment(QCD, &[0, 0]));
    bytes.extend(segment(QCC, &[0, 0, 0]));
    bytes.extend(segment(CRG, &[0, packet_length_mode, 0, roi_shift]));
    bytes.extend(segment(DFS, &[0, 1, 1, 0x40]));
    bytes.extend(segment(
        ADS,
        &[2, 1, 0x40, 1, (packet_length_mode & 3) << 6],
    ));
    bytes.extend(segment(
        NLT,
        &[
            0xff,
            0xff,
            7,
            if packet_length_mode & 1 == 0 { 0 } else { 3 },
        ],
    ));
    bytes.extend(segment(CBD, &[0, 1, 7]));
    let mut atk = vec![0x4c, 2];
    atk.extend_from_slice(&(0x3fff_u128 << 112).to_be_bytes());
    atk.push(0);
    bytes.extend(segment(ATK, &atk));
    bytes.extend(segment(RGN, &[0, 0, roi_shift]));
    let mut matrix = 0_u16.to_be_bytes().to_vec();
    matrix.extend_from_slice(&0x0101_u16.to_be_bytes());
    matrix.extend_from_slice(&0_u16.to_be_bytes());
    matrix.extend_from_slice(&1_i16.to_be_bytes());
    bytes.extend(if roi_shift & 0x40 == 0 {
        segment(MCT, &matrix)
    } else {
        segmented_mct(&matrix, 1)
    });
    let mut offset = 0_u16.to_be_bytes().to_vec();
    offset.extend_from_slice(&0x0202_u16.to_be_bytes());
    offset.extend_from_slice(&0_u16.to_be_bytes());
    offset.extend_from_slice(&i16::from(roi_shift).to_be_bytes());
    bytes.extend(segment(MCT, &offset));
    let mcc_payload = [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1];
    bytes.extend(if roi_shift & 0x40 == 0 {
        segment(MCC, &mcc_payload)
    } else {
        segmented_mcc(&mcc_payload, 4)
    });
    if roi_shift & 0x20 != 0 {
        let mut matrix64 = 0_u16.to_be_bytes().to_vec();
        matrix64.extend_from_slice(&0x0d03_u16.to_be_bytes());
        matrix64.extend_from_slice(&0_u16.to_be_bytes());
        matrix64.extend_from_slice(&1.25_f64.to_bits().to_be_bytes());
        bytes.extend(segment(MCT, &matrix64));
        bytes.extend(segment(
            MCC,
            &[0, 0, 2, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 3],
        ));
        bytes.extend(segment(MCO, &[2, 1, 2]));
    } else {
        bytes.extend(segment(MCO, &[1, 1]));
    }

    fn segmented_mct(payload: &[u8], split: usize) -> Vec<u8> {
        let mut out = Vec::new();
        let mut first = payload[..4].to_vec();
        first.extend_from_slice(&1_u16.to_be_bytes());
        first.extend_from_slice(&payload[6..6 + split]);
        out.extend(segment(MCT, &first));
        let mut second = 1_u16.to_be_bytes().to_vec();
        second.extend_from_slice(&payload[2..4]);
        second.extend_from_slice(&payload[6 + split..]);
        out.extend(segment(MCT, &second));
        out
    }

    fn segmented_mcc(payload: &[u8], split: usize) -> Vec<u8> {
        let mut out = Vec::new();
        let mut first = payload[..3].to_vec();
        first.extend_from_slice(&1_u16.to_be_bytes());
        first.extend_from_slice(&payload[5..7]);
        first.extend_from_slice(&payload[7..7 + split]);
        out.extend(segment(MCC, &first));
        let mut second = 1_u16.to_be_bytes().to_vec();
        second.push(payload[2]);
        second.extend_from_slice(&payload[7 + split..]);
        out.extend(segment(MCC, &second));
        out
    }
    let poc = [0, 0, 0, 1, 1, 1, packet_length_mode % 5];
    if packet_length_mode & 8 == 0 {
        bytes.extend(segment(POC, &poc));
    }
    let packed_header = if packet_length_mode & 2 != 0 {
        &[0_u8][..]
    } else {
        &[][..]
    };
    let logical_packet_length = tile_data.len().saturating_add(packed_header.len());
    let encoded_packet_length =
        encode_packet_length(u32::try_from(logical_packet_length).unwrap_or(u32::MAX));
    if packet_length_mode & 1 == 0 {
        let mut plm = vec![0];
        plm.push(u8::try_from(encoded_packet_length.len()).unwrap());
        plm.extend_from_slice(&encoded_packet_length);
        bytes.extend(segment(PLM, &plm));
    }
    if packet_length_mode & 6 == 2 {
        let mut ppm = vec![0];
        ppm.extend_from_slice(&u32::try_from(packed_header.len()).unwrap().to_be_bytes());
        ppm.extend_from_slice(packed_header);
        bytes.extend(segment(PPM, &ppm));
    }
    let tile_part_start = bytes.len();
    let mut sot_payload = Vec::new();
    sot_payload.extend_from_slice(&0_u16.to_be_bytes());
    sot_payload.extend_from_slice(&0_u32.to_be_bytes());
    sot_payload.extend_from_slice(&[0, 1]);
    bytes.extend(segment(SOT, &sot_payload));
    bytes.extend(segment(COC, &[0, 0, 0, 2, 2, 0, 1]));
    bytes.extend(segment(QCD, &[0x40, 0x40]));
    bytes.extend(segment(QCC, &[0, 0x40, 0x48]));
    if roi_shift & 0x60 == 0x60 {
        let mut tile_matrix = 0_u16.to_be_bytes().to_vec();
        tile_matrix.extend_from_slice(&0x0101_u16.to_be_bytes());
        tile_matrix.extend_from_slice(&0_u16.to_be_bytes());
        tile_matrix.extend_from_slice(&2_i16.to_be_bytes());
        bytes.extend(segment(MCT, &tile_matrix));
        bytes.extend(segment(MCO, &[2, 2, 1]));
    }
    if packet_length_mode & 8 != 0 {
        bytes.extend(segment(POC, &poc));
    }
    if packet_length_mode & 1 != 0 {
        let mut plt = vec![0];
        plt.extend_from_slice(&encoded_packet_length);
        bytes.extend(segment(PLT, &plt));
    }
    if packet_length_mode & 6 == 6 {
        let mut ppt = vec![0];
        ppt.extend_from_slice(packed_header);
        bytes.extend(segment(PPT, &ppt));
    }
    bytes.extend_from_slice(&SOD.to_be_bytes());
    bytes.extend_from_slice(tile_data);
    let tile_part_length = u32::try_from(bytes.len() - tile_part_start).unwrap();
    bytes[tile_part_start + 6..tile_part_start + 10]
        .copy_from_slice(&tile_part_length.to_be_bytes());
    bytes.extend_from_slice(&EOC.to_be_bytes());
    bytes
}

fn encode_packet_length(length: u32) -> Vec<u8> {
    if length == 0 {
        return Vec::new();
    }
    let mut groups = [0_u8; 5];
    let mut value = length;
    let mut start = groups.len() - 1;
    groups[start] = u8::try_from(value & 0x7f).unwrap();
    value >>= 7;
    while value != 0 {
        start = start.checked_sub(1).unwrap();
        groups[start] = u8::try_from(value & 0x7f).unwrap() | 0x80;
        value >>= 7;
    }
    groups[start..].to_vec()
}

fn make_jp2(
    codestream_bytes: &[u8],
    width: u32,
    height: u32,
    length_form: u8,
    palette_mapping: bool,
) -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    bytes.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut jp2_header = box32(*b"ihdr", &image_header);
    jp2_header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 16]));
    if palette_mapping {
        let mut palette = 256_u16.to_be_bytes().to_vec();
        palette.extend_from_slice(&[1, 7]);
        for value in 0_u16..256 {
            palette.push(u8::try_from(value).unwrap());
        }

        jp2_header.extend(box32(*b"pclr", &palette));
        jp2_header.extend(box32(*b"cmap", &[0, 0, 1, 0]));
        jp2_header.extend(box32(*b"cdef", &[0, 1, 0, 0, 0, 0, 0, 1]));
    }
    bytes.extend(box32(*b"jp2h", &jp2_header));
    match length_form {
        0 => bytes.extend(box32(*b"jp2c", codestream_bytes)),
        1 => {
            bytes.extend_from_slice(&1_u32.to_be_bytes());
            bytes.extend_from_slice(b"jp2c");
            bytes.extend_from_slice(
                &u64::try_from(16 + codestream_bytes.len())
                    .unwrap()
                    .to_be_bytes(),
            );
            bytes.extend_from_slice(codestream_bytes);
        }
        _ => {
            bytes.extend_from_slice(&0_u32.to_be_bytes());
            bytes.extend_from_slice(b"jp2c");
            bytes.extend_from_slice(codestream_bytes);
        }
    }
    bytes
}

fn make_static_jpx(codestream_bytes: &[u8], width: u32, height: u32, mode: u8) -> Vec<u8> {
    let mut bytes = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    bytes.extend(box32(*b"ftyp", b"jpxb\0\0\0\0jpxb"));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    bytes.extend(box32(*b"jp2h", &header));
    bytes.extend(box32(*b"jpch", &header));
    let mut registration = 2_u16.to_be_bytes().to_vec();
    registration.extend_from_slice(&1_u16.to_be_bytes());
    registration.extend_from_slice(&0_u16.to_be_bytes());
    registration.extend_from_slice(&[2, 1, mode & 1, 0]);
    bytes.extend(box32(*b"jplh", &box32(*b"creg", &registration)));
    let mut options = height.to_be_bytes().to_vec();
    options.extend_from_slice(&width.to_be_bytes());
    options.push(0);
    let mut composition = box32(*b"copt", &options);
    if mode & 2 != 0 {
        let mut instruction = 5_u16.to_be_bytes().to_vec();
        instruction.extend_from_slice(&0_u16.to_be_bytes());
        instruction.extend_from_slice(&1_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        instruction.extend_from_slice(&1_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        composition.extend(box32(*b"inst", &instruction));
    }
    bytes.extend(box32(*b"comp", &composition));
    bytes.extend(box32(*b"jp2c", codestream_bytes));
    bytes
}

fn segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&u16::try_from(payload.len() + 2).unwrap().to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn box32(box_type: [u8; 4], payload: &[u8]) -> Vec<u8> {
    let mut bytes = u32::try_from(8 + payload.len())
        .unwrap()
        .to_be_bytes()
        .to_vec();
    bytes.extend_from_slice(&box_type);
    bytes.extend_from_slice(payload);
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structured_positive_generators_admit_empty_input_and_all_selectors() {
        exercise_structured_framing(&[]);
        for selector in 0..=u8::MAX {
            exercise_structured_framing(&[0, 0, selector, 0]);
        }
    }
}
