//!
//! This implements the Chaum-Pedersen Zero-Knowledge protocol for proof of
//! discrete log over two generators as a password authentication protocol. See,
//! for example, here: https://www.cs.umd.edu/~waa/414-F11/IntroToCrypto.pdf
//!
//! WARNING: This is research code, and must not be used in real-world systems

use std::io;
use std::io::Write;

use rand::Rng;
use rand::prelude::StdRng;
use rand_core::SeedableRng;
use sha256::digest;
use rpassword::read_password;

use mod_exp::mod_exp; // fast modular exp

// set up the public values, used only for this example
pub const ORDER:u64 = 4294967029;   // a 32-bit "safe prime"
pub const GROUP_GEN_G: u64 = 10324;  // every element prime order group is 
pub const GROUP_GEN_H: u64 = 83981;   // a generator, so we choose two "random" ones

// for elliptic curves, we will use Edward's style Curve25519
// use curve25519_dalek::constants::BASEPOINT_ORDER;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE; // for fast mult to basepoint
pub const CURVE_GEN_G: i64 = 10324; // we multiply scalars to the curve's basepoint
pub const CURVE_GEN_H: i64 = 83981; // to obtain two generators on this curve


struct User<'a> {
    name: &'a str,
    secret: Option<String>,
}

fn main() {
    // Collect user credentials and authenticate with Chaum-Pedersen Protocol.
    //
    let mut name = String::new();
    let user = _get_user_credentials(&mut name);
    let secret = user.secret
                    .clone()
                    .expect("Conversion failed")
                    .to_string();

    let k: u64 = secret                 // user's secret from registration
                        .parse::<u64>() // appropriately handle
                        .unwrap();      // exception here
    // NOTE: for this example, assume user enters a numerical string
    // in practice we may pseudorandomly expand from a password string.

    assert!(fs_chaum_pedersen(&mut name, &k, "CURVE")); // set to GROUP or CURVE
    println!("Success!");

}

fn _get_user_credentials<'a>(name: &'a mut String) -> User<'_> {
    // Subroutine to collect user input and pack into the struct
    //
    // arguments:
    // name: &'a mut String    -   the username object, empty.
    // returns: (User<'_>) the user input in a custom datatype.
    //
    print!("username: ");
    io::stdout().flush().expect("Flush failed.");
    io::stdin()
        .read_line(name)
        .expect("Read failed.");

    print!("password: ");
    std::io::stdout().flush().unwrap();
    let secret = read_password().unwrap();

    User{
        name: name, 
        secret: Some(String::from(secret))
    }
}

fn fs_chaum_pedersen(name: &mut String, k: &u64, mode: &str) -> bool {
    // Calls the appropriate subroutine based on mode or exits.
    //
    // arguments:
    // name: &mut String   -   username, to be hashed.
    // k: &u64             -   user's registration secret key, accepted as input.
    // mode: &str          -   Chaum-Pedersen on GROUP or CURVE.
    // returns: (bool) truth value of the authentication procedure.
    //
    match mode {
        "GROUP" => {
            _grp_chaum_pedersen(&name, &k)
        }, 
        "CURVE" => {
            _curv_chaum_pedersen(name, &(*k as i64))
        }
        _ => {
                println!("Invalid input");
                false
        }
    }
}

fn _grp_chaum_pedersen(name: &String, k1: &u64) -> bool {
    // Chaum-Pedersen protocol on group Zq of prime order q = 4294967029
    // choice of q is arbitrary and for this example only.
    //
    // arguments:
    // name: &mut String   -   username, to be hashed.
    // k1: &u64             -  user's registration secret key, accepted as input.
    // returns: (bool) truth value of the authentication procedure.
    //
    let k2: u64 = _get_session_secret() % (ORDER - 1);  // generate session secret
    // usual pubk computation
    let y1 = mod_exp(GROUP_GEN_G, *k1, ORDER);
    let y2 = mod_exp(GROUP_GEN_H, *k1, ORDER);
    let r1 = mod_exp(GROUP_GEN_G, k2, ORDER);
    let r2 = mod_exp(GROUP_GEN_H, k2, ORDER);
    let mut mesg: String = name.clone().to_owned();

    // concatenate message strings to for Fiat-Shamir transformation
    mesg = mesg + "|" + &GROUP_GEN_G.to_string() + "|" 
            + &GROUP_GEN_H.to_string() + "|" + &y1.to_string() + "|" 
            + &y2.to_string() + "|" + &r1.to_string() + "|" + &r2.to_string();
    // obtain the verification challenge
    let ch: u64 = _fiat_shamir_transform(&mesg) % (ORDER - 1);
    let pf: u64 = _safe_mod_subtract(k2, ch * k1 % (ORDER - 1), ORDER - 1);

    // the verifier would know the public keys, for this example we pass them
    // also send elements r1 and r2 as the proof, which is required
    let password = vec![y1, y2, r1, r2, pf];
    _grp_verify(name, &password)
}

fn _grp_verify(name: &String, vec_elems: &Vec<u64>) -> bool {
    // Verification for the Chaum-Pedersen protocol on group Zq of prime order 
    // q = 4294967029.
    // 
    // arguments:
    // name: &mut String   -   username, to be hashed.
    // password: &Vec<u64> -   the password as a vector of group elements
    //                         needed for proof verification.
    //
    // returns: (bool) the result of the verification.
    //
    let mut mesg: String = name.clone().to_owned();
    
    // recreate the message string and perform Fiat-Shamir transformation
    mesg = mesg + "|" + &GROUP_GEN_G.to_string() + "|" 
            + &GROUP_GEN_H.to_string() + "|" + &vec_elems[0].to_string() + "|" 
            + &vec_elems[1].to_string() + "|" + &vec_elems[2].to_string() + "|" 
            + &vec_elems[3].to_string();

    // recreate the challenge
    let ch: u64 = _fiat_shamir_transform(&mesg)  % ORDER;
    
    // verification 1: (g^s) * (y1 ^ c) % q = r1
    let _r1 = (mod_exp(GROUP_GEN_G, vec_elems[4], ORDER) * mod_exp(vec_elems[0], ch, ORDER)) % ORDER;
    // verification 2: (h^s) * (y2 ^ c) % q = r2
    let _r2 = (mod_exp(GROUP_GEN_H, vec_elems[4], ORDER) * mod_exp(vec_elems[1], ch, ORDER)) % ORDER;

    // compare values received with computed values and return result
    if (vec_elems[2] == _r1) & (vec_elems[3] == _r2) {
        true
    }
    else {
        false
    }
}

fn _curv_chaum_pedersen(name: &mut String, k1: &i64) -> bool {
    // Chaum-Pedersen protocol on Edward's style Curve25519.
    //
    // arguments:
    // name: &mut String   -   username, to be hashed.
    // k1: &u64             -  user's registration secret key, accepted as input.
    // returns: (bool) truth value of the authentication procedure.
    //
    let k2: i64 = _get_session_secret() as i64;   // generate session secret
    
    // curve computation requires special Scalar values
    let scal_k1 = _i64_to_scalar(&k1);
    let scal_k2 = _i64_to_scalar(&k2);
    let scal_g =_i64_to_scalar(&CURVE_GEN_G);
    let scal_h =_i64_to_scalar(&CURVE_GEN_H);

    // usual pubk computation on the curve
    let point_y1: EdwardsPoint = &scal_k1 * (&scal_g * &ED25519_BASEPOINT_TABLE);
    let point_y2: EdwardsPoint = &scal_k1 * (&scal_h * &ED25519_BASEPOINT_TABLE);
    let point_r1: EdwardsPoint = &scal_k2 * (&scal_g * &ED25519_BASEPOINT_TABLE);
    let point_r2: EdwardsPoint = &scal_k2 * (&scal_h * &ED25519_BASEPOINT_TABLE);
    
    // convert to byte values to send ; TODO: this could be compressed
    let y1: [u8; 32] = point_y1.to_montgomery().to_bytes();
    let y2: [u8; 32] = point_y2.to_montgomery().to_bytes();
    let r1: [u8; 32] = point_r1.to_montgomery().to_bytes();
    let r2: [u8; 32] = point_r2.to_montgomery().to_bytes();
    let mut mesg: String = name.clone().to_owned();
    
    // concatenate message strings to for Fiat-Shamir transformation
    // TODO: cleaner representation with Vec<_>
    mesg = mesg + "|" + &CURVE_GEN_G.to_string() + "|" 
            + &CURVE_GEN_H.to_string() + "|" + &_bytes_to_string(&y1) + "|" 
            + &_bytes_to_string(&y2) + "|" + &_bytes_to_string(&r1) + "|" 
            + &_bytes_to_string(&r2);

    // obtain the verification challenge and convert to Scalar
    let ch: i64 = _fiat_shamir_transform(&mesg) as i64;
    let scal_ch = _i64_to_scalar(&ch);
    let scal_pf: Scalar = scal_k2 - (scal_ch * scal_k1);
    
    // the verifier would know the public keys, for this example we pass them
    let mut vec_points = vec![point_y1, point_y2, point_r1, point_r2];

    // also send points r1 and r2 as the proof, which is required
    _curv_verify(name, &vec_points, &scal_pf)
}

fn _curv_verify(
                name: &String,  
                vec_points: &Vec<EdwardsPoint>, 
                scal_pf: &Scalar,
            ) -> bool {
    // Verification for the Chaum-Pedersen protocol on on Edward's style 
    //Curve25519.
    // 
    // name: &mut String               -   username, to be hashed.
    // vec_points: &Vec<EdwardsPoint>  -   a vector of curve points y1, y2, r1, r2.
    //
    // scal_pf: &Scalar                - the proof scalar, `s`.
    // returns: (bool) the result of the verification.
    //
    // compute the scalar basepoint multiplicands
    let scal_g =_i64_to_scalar(&CURVE_GEN_G);
    let scal_h =_i64_to_scalar(&CURVE_GEN_H);
    
    // recompute the necessary values for Fiat-Shamir transform
    let y1: [u8; 32] = vec_points[0].to_montgomery().to_bytes();
    let y2: [u8; 32] = vec_points[1].to_montgomery().to_bytes();
    let r1: [u8; 32] = vec_points[2].to_montgomery().to_bytes();
    let r2: [u8; 32] = vec_points[3].to_montgomery().to_bytes();
    let mut mesg: String = name.clone().to_owned();

    // recreate the message string and perform Fiat-Shamir transformation
    mesg = mesg + "|" + &CURVE_GEN_G.to_string() + "|" 
            + &CURVE_GEN_H.to_string() + "|" + &_bytes_to_string(&y1) + "|" 
            + &_bytes_to_string(&y2) + "|" + &_bytes_to_string(&r1) + "|" 
            + &_bytes_to_string(&r2);
    
    // recreate the challenge and convert to Scalar
    let ch: i64 = _fiat_shamir_transform(&mesg) as i64;
    let scal_ch = _i64_to_scalar(&ch);
    
    // verification 1: [s] * G + [c] * y1 = r1
    let _point_r1 = (scal_pf * (&scal_g * &ED25519_BASEPOINT_TABLE)) + (&scal_ch * vec_points[0]);
    // verification 2: [s] * H + [c] * y2 = r2
    let _point_r2 = (scal_pf * (&scal_h * &ED25519_BASEPOINT_TABLE)) + (&scal_ch * vec_points[1]);

    // compare values received with computed values and return result
    if (_point_r1 == vec_points[2]) & (_point_r2 == vec_points[3]) {
        true
    }
    else {
        false
    }
}

fn _fiat_shamir_transform(mesg: &String) -> u64 {
    // The Fiat-Shamir protocol can be used to convert any 3-round Sigma 
    // protocol with public coins into a 1-round protocol secure in the ROM; 
    // in practice a hash function is used.
    // 
    // mesg: &String   -   the string to be hashed into the challenge.
    // returns: (u64) the verifier's challenge value.
    //
    let chal_str = digest(mesg.clone());
    let chal_str = &chal_str[..8]; // take the first 32 bits
    let chal_int = u64::from_str_radix(&chal_str, 16); // interpret as base 10
    chal_int.unwrap()
}

fn _bytes_to_string(bytes: &[u8]) -> String {
    // Lazy helper function for type conversion
    bytes.into_iter().map(|i| i.to_string() + " ").collect::<String>()
}

fn _string_to_bytes(s: &String) -> Vec<u8> {
    // Lazy helper function for type conversion
    s.split_whitespace().map(|s| s.trim())
    .filter(|s| !s.is_empty())
    .map(|s| s.parse().unwrap())
    .collect()
}

fn _i64_to_scalar(val: &i64) -> Scalar {
    // Lazy helper function for type conversion.
    let mut canonical_bytes: [u8; 32] = [0; 32];
    canonical_bytes[..8].clone_from_slice(&val.to_le_bytes());
    Scalar::from_canonical_bytes(canonical_bytes).unwrap()
}

fn _scalar_to_i64(point: &Scalar) -> i64 {
    // Lazy helper function for type conversion.
    let mut slice_point: [u8; 8] = [0; 8];
    slice_point.clone_from_slice(&point.to_bytes()[..8]);
    i64::from_be_bytes(slice_point)
}

fn _get_session_secret() -> u64 {
    // Pseudorandomly generate a session secret from entropy.
    let mut rng = StdRng::from_entropy(); // securely seed a PRG from fresh entropy
    let num: u64 = rng.gen();
    num
}

fn _safe_mod_subtract(a: u64, b: u64, m: u64) -> u64 {
    // Stable modular subtration for unsigned integers -- prevents
    // numerical overflow.
    let c = (((-1 * b as i128)).rem_euclid(m  as i128)) as u64;
    a + c % m
}
