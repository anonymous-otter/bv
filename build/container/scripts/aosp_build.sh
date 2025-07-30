set -e

export TARGET_BUILD_TYPE=release
export HOST_BUILD_TYPE=release

source build/envsetup.sh
lunch aosp_oriole-userdebug

# Translate Dafny code (out of the build system)
pushd system/bt/stack/l2cap/bv/

dafny translate cpp \
    --allow-warnings --unicode-char false --no-verify \
    --output ./generated/generated_partial.cpp \
    ./dfyconfig.toml extern_defs.h generated_partial.h
# Manual modifications to mitigate problems in the translation
sed -i 's/::L_LOG/L_LOG/g' ./generated/generated_partial.cpp
# Find all instances of extern_types::NativeHandle<T> handle = extern_types::get_NativeHandle_default()
# And add the explicit type to the right hand
find_pat='extern_types::NativeHandle\s*<([a-zA-Z0-9_:<>]+)>\s*handle\s*=\s*extern_types::get_NativeHandle_default\(\)'
replace_pat='extern_types::NativeHandle<\1> handle = extern_types::get_NativeHandle_default<\1>()'
sed -i -E "s/$find_pat/$replace_pat/g" ./generated/the_pro.h

popd

mmm system/bt -j$(nproc --all)