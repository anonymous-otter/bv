set -e

# Uncomment if you want to use a private repo on github
# mkdir -p -m 0700 ~/.ssh && ssh-keyscan github.com >> ~/.ssh/known_hosts

AOSP_MANIFEST_REPO_URL="https://github.com/anonymous-otter/bv-manifest.git"
# No need to provide the -b flag, as the default branch is set in our manifest
repo init --partial-clone --no-use-superproject --clone-filter=blob:limit=10M -u ${AOSP_MANIFEST_REPO_URL}
repo sync -c -j $(nproc --all)

# Download proprietary binaries
# Source: https://source.android.com/docs/setup/download#downloading-proprietary-binaries
# List: https://developers.google.com/android/drivers
# We use the image for Google Pixel 6 and Android 12.1.0
PROP_BIN_URL="https://dl.google.com/dl/android/aosp/google_devices-oriole-sq3a.220705.001.b2-f0b4ace1.tgz"
wget ${PROP_BIN_URL} -O /tmp/prop_bin.tgz && \
    tar -xzf /tmp/prop_bin.tgz -C . && \
    rm /tmp/prop_bin.tgz && \
    ./extract-google_devices-oriole.sh && \
    rm extract-google_devices-oriole.sh

