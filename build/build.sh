#! /usr/bin/bash

set -x -e

pushd $(dirname "$0")/container

container_workdir="/workspaces/bv_aosp"
workdir="./work"

IMAGE_NAME="bv_aosp"

docker build -t $IMAGE_NAME .

mkdir -p $workdir

common_options=(
    "--rm"
    "--interactive" "--tty"
    "--mount" "type=bind,src=$workdir,dst=$container_workdir"
    "--workdir" "$container_workdir"
)

docker run \
    ${common_options[@]} \
    -v ~/.gitconfig:/etc/gitconfig `# Making the global gitconfig available in the container.` \
    `#-v $SSH_AUTH_SOCK:/ssh-agent -e SSH_AUTH_SOCK=/ssh-agent` `# Uncomment if you need ssh for cloning` \
    $IMAGE_NAME \
    bash "/root/scripts/aosp_clone.sh"

docker run \
    ${common_options[@]} \
    $IMAGE_NAME \
    bash "/root/scripts/aosp_build.sh"

popd