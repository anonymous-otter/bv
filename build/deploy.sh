#! /usr/bin/bash

set -e

script_dir=$(dirname "$0")

container_dir="$script_dir/container"

workdir="./work"
aosp_out="$workdir/out"
target_out="$aosp_out/target/product/oriole/system"

if [ -f "$container_dir/$target_out/lib/libbluetooth.so" ]; then
    IMAGE_NAME="bv_aosp"
    container_workdir="/workspaces/bv_aosp"
    pushd $container_dir

    set -x
    docker run \
        --rm \
        --interactive --tty \
        --mount type=bind,src=$workdir,dst=$container_workdir \
        --workdir $container_workdir \
        --device /dev/bus/usb \
        $IMAGE_NAME \
        bash "/root/scripts/bv_deploy.sh" "$target_out"
    
    popd
else
    echo "Target binary not found: $container_dir/$target_out"
    echo "Using the prebuilt version"

    target_out=$script_dir/prebuilt

    if [ ! -f "$target_out/lib/libbluetooth.so" ]; then
        echo "Error: $target_out/lib/libbluetooth.so not found"
        exit 1
    fi

    bash "$container_dir/scripts/bv_deploy.sh" "$target_out"
fi