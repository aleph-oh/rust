use std::path::PathBuf;

use crate::spec::base::apple::{macos_llvm_target, opts, Arch};
use crate::spec::{Cc, FramePointer, LinkerFlavor, Lld, SanitizerSet, Target, TargetOptions};

// Read the environment variable OPENCILK_RT_SEARCH_DIR to get the path to the OpenCilk runtime for
// this target.
// FIXME(jhilton): we should have default search paths for this so that we don't need to bother with
// having users set an environment variable.
fn opencilk_runtime_search_directory() -> PathBuf {
    let path = std::env::var("OPENCILK_RT_SEARCH_DIR").expect("OPENCILK_RT_SEARCH_DIR must be set");
    PathBuf::from(path)
}

pub fn target() -> Target {
    let arch = Arch::Arm64;
    let mut base = opts("macos", arch);
    base.cpu = "apple-m1".into();
    base.max_atomic_width = Some(128);

    // FIXME: The leak sanitizer currently fails the tests, see #88132.
    base.supported_sanitizers = SanitizerSet::ADDRESS | SanitizerSet::CFI | SanitizerSet::THREAD;

    let mut late_link_args = std::collections::BTreeMap::new();
    let opencilk_runtime_path = opencilk_runtime_search_directory()
        .into_os_string()
        .into_string()
        .expect("OpenCilk runtime path should contain only valid unicode!");
    let set_rpath = format!("-Wl,-rpath,{}", opencilk_runtime_path);
    let args_to_link_opencilk: Vec<std::borrow::Cow<'static, str>> = vec![
        "-L".into(),
        opencilk_runtime_path.into(),
        "-lopencilk_osx_dynamic".into(),
        set_rpath.into(),
    ];
    late_link_args.insert(LinkerFlavor::Darwin(Cc::Yes, Lld::No), args_to_link_opencilk.clone());
    Target {
        // Clang automatically chooses a more specific target based on
        // MACOSX_DEPLOYMENT_TARGET. To enable cross-language LTO to work
        // correctly, we do too.
        llvm_target: macos_llvm_target(arch).into(),
        pointer_width: 64,
        data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
        arch: arch.target_arch(),
        options: TargetOptions {
            mcount: "\u{1}mcount".into(),
            frame_pointer: FramePointer::NonLeaf,
            late_link_args,
            ..base
        },
    }
}
