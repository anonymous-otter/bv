set -e

device_id=$(adb shell getprop ro.serialno)

if [ -z "$device_id" ]; then
    echo "Device not found"
    exit 1
fi

echo "Device Id: $device_id"

adb -s $device_id root 
adb -s $device_id remount

target_out=$1

echo "Last modified date of file:"
date -r $target_out/lib64/libbluetooth.so

adb -s $device_id push $target_out/lib/libbluetooth.so /system/lib/
adb -s $device_id push $target_out/lib64/libbluetooth.so /system/lib64/

adb -s $device_id reboot