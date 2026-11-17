//! Test-only secp256k1 input generator for the approved nonce scan.
//! Opt-in: compiled only with RUSTFLAGS="--cfg nonce_openssl" (links libcrypto); the default test build uses the inherited affine model.
//! The first accepted shots are compared against the inherited affine model.
use std::ffi::{c_char, c_int, c_void, CString};
use ruint::aliases::U256;

#[link(name = "crypto")]
unsafe extern "C" {
    fn OBJ_txt2nid(s: *const c_char) -> c_int;
    fn EC_GROUP_new_by_curve_name(nid: c_int) -> *mut c_void;
    fn EC_GROUP_free(group: *mut c_void);
    fn EC_POINT_new(group: *const c_void) -> *mut c_void;
    fn EC_POINT_free(point: *mut c_void);
    fn EC_POINT_mul(group: *const c_void, r: *mut c_void, n: *const c_void,
                    q: *const c_void, m: *const c_void, ctx: *mut c_void) -> c_int;
    fn EC_POINT_add(group: *const c_void, r: *mut c_void, a: *const c_void,
                    b: *const c_void, ctx: *mut c_void) -> c_int;
    fn EC_POINT_cmp(group: *const c_void, a: *const c_void, b: *const c_void,
                    ctx: *mut c_void) -> c_int;
    fn EC_POINT_is_at_infinity(group: *const c_void, point: *const c_void) -> c_int;
    fn EC_POINT_get_affine_coordinates(group: *const c_void, point: *const c_void,
                                       x: *mut c_void, y: *mut c_void, ctx: *mut c_void) -> c_int;
    fn BN_CTX_new() -> *mut c_void;
    fn BN_CTX_free(ctx: *mut c_void);
    fn BN_new() -> *mut c_void;
    fn BN_free(bn: *mut c_void);
    fn BN_bin2bn(bytes: *const u8, len: c_int, ret: *mut c_void) -> *mut c_void;
    fn BN_bn2binpad(bn: *const c_void, bytes: *mut u8, len: c_int) -> c_int;
}

pub(super) struct Curve {
    group: *mut c_void,
    ctx: *mut c_void,
    points: [*mut c_void; 3],
    scalars: [*mut c_void; 2],
    coords: [*mut c_void; 2],
}

impl Curve {
    pub(super) fn new() -> Self {
        unsafe {
            let name = CString::new("secp256k1").unwrap();
            let group = EC_GROUP_new_by_curve_name(OBJ_txt2nid(name.as_ptr()));
            let ctx = BN_CTX_new();
            assert!(!group.is_null() && !ctx.is_null());
            let points = std::array::from_fn(|_| EC_POINT_new(group));
            let scalars = std::array::from_fn(|_| BN_new());
            let coords = std::array::from_fn(|_| BN_new());
            assert!(points.iter().chain(scalars.iter()).chain(coords.iter()).all(|p| !p.is_null()));
            Self { group, ctx, points, scalars, coords }
        }
    }

    fn affine(&self, point: *mut c_void) -> (U256, U256) {
        unsafe {
            assert_eq!(EC_POINT_get_affine_coordinates(self.group, point, self.coords[0], self.coords[1], self.ctx), 1);
            let mut x = [0u8; 32];
            let mut y = [0u8; 32];
            assert_eq!(BN_bn2binpad(self.coords[0], x.as_mut_ptr(), 32), 32);
            assert_eq!(BN_bn2binpad(self.coords[1], y.as_mut_ptr(), 32), 32);
            (U256::from_be_bytes(x), U256::from_be_bytes(y))
        }
    }

    /// None uses the same rejection conditions as payload_predict_nonce.
    pub(super) fn points(&self, random_le: &[[u8; 32]; 2]) -> Option<[(U256, U256); 3]> {
        unsafe {
            for i in 0..2 {
                let mut be = random_le[i];
                be.reverse();
                assert_eq!(BN_bin2bn(be.as_ptr(), 32, self.scalars[i]), self.scalars[i]);
                assert_eq!(EC_POINT_mul(self.group, self.points[i], self.scalars[i],
                                        std::ptr::null(), std::ptr::null(), self.ctx), 1);
            }
            let eq = EC_POINT_cmp(self.group, self.points[0], self.points[1], self.ctx);
            assert!(eq >= 0);
            if eq == 0 || self.points[..2].iter().any(|&p| EC_POINT_is_at_infinity(self.group, p) == 1) {
                return None;
            }
            assert_eq!(EC_POINT_add(self.group, self.points[2], self.points[0], self.points[1], self.ctx), 1);
            Some([self.affine(self.points[0]), self.affine(self.points[1]), self.affine(self.points[2])])
        }
    }
}

impl Drop for Curve {
    fn drop(&mut self) {
        unsafe {
            for p in self.points { EC_POINT_free(p); }
            for b in self.scalars.into_iter().chain(self.coords) { BN_free(b); }
            BN_CTX_free(self.ctx);
            EC_GROUP_free(self.group);
        }
    }
}
