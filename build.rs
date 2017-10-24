extern crate cc;

fn main() {
    use cc::Build;
    Build::new()
        .cpp(true)
        .file("src/edit_distance.cc")
        .file("src/metrics.cc")        
        .file("src/util.cc")        
        .include("src")
        .compile("ninja_util");
    return;

    Build::new()
        .cpp(true)
        .file("src/build.cc")
        .file("src/build_log.cc")
        .file("src/clean.cc")
        .file("src/clparser.cc")
        .file("src/debug_flags.cc")
        .file("src/depfile_parser.cc")
        .file("src/deps_log.cc")
        .file("src/disk_interface.cc")
        .file("src/edit_distance.cc")
        .file("src/eval_env.cc")
        .file("src/graph.cc")
        .file("src/graphviz.cc")
        .file("src/lexer.cc")
        .file("src/line_printer.cc")
        .file("src/manifest_parser.cc")
        .file("src/metrics.cc")
        .file("src/state.cc")
        .file("src/string_piece_util.cc")
        .file("src/util.cc")
        .file("src/version.cc")
        .file("src/subprocess-win32.cc")
        .file("src/includes_normalize-win32.cc")
        .file("src/msvc_helper-win32.cc")
        .file("src/msvc_helper_main-win32.cc")
        .file("src/minidump-win32.cc")
        .file("src/getopt.c")
        .include("src")
        .compile("ninja");
    
     Build::new()
        .cpp(true)
        .file("src/ninja.cc")
        .include("src")
        .compile("ninja_main");
}