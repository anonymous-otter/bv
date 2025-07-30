# BV

BV is a formally verified implementation of the L2CAP (Logical Link Control and Adaptation Protocol) state machine,
developed in [Dafny](https://dafny.org/).
It verifies that the implementation conforms to the Bluetooth specification through refinement.
It also proves important safety and liveness properties, e.g., under the fairness assumption, the state machine will eventually 
reach either `Open` or `Destroyed` state, indicating that a Bluetooth connection has been established or terminated, respectively.

## Code Structure

The following outlines the key components of the BV source code:
```
BV/
├── spec/
│   ├── SpecStateMachine.s.dfy     # Specification State Machine (SSM)
│   └── Events.s.dfy               # Event classification and helpers for SSM
├── impl/
│   ├── OpsStateMachine.i.dfy      # Operational State Machine (OSM)
│   └── csm/                       # Verified L2CAP state machine implementation
├── proof/
│   ├── RefinementProof.i.dfy      # Proof that OSM refines SSM
│   ├── SafetyProof.i.dfy          # Proof of safety properties
│   └── LivenessProof.i.dfy        # Proof of liveness properties
├── build/                         # Build scripts for compiling and integrating BV with Android
├── CommonTypes.i.dfy              # Shared types used across components
└── dfyconfig.toml                 # Dafny project configuration
```

### `spec/` — Specification Components

This directory contains the trusted specification of the L2CAP state machine. It includes:
- The Specification State Machine (SSM) model that defines allowed behaviors.
- Event classification logic, specifying which events are valid, invalid, or error events.

These components serve as the basis for verifying the correctness of the implementation and proving refinement, safety, and liveness.

### `impl/` — Implementation Components

This directory holds the Operational State Machine (OSM) and the verified implementation of the L2CAP state machine under the csm/ subdirectory. The OSM serves as an abstraction of the actual implementation, structured in a way that facilitates formal verification.

### `proof/` — Proof Artifacts

This directory contains the formal verification proofs that:
- The implementation refines the specification.
- The system is safe (e.g., no invalid transitions).
- The system is live (e.g., can always make progress).

These proofs are written in Dafny and ensure that the implementation adheres to the expected correctness guarantees.

### `build/` — Build Scripts
This directory contains scripts and configurations for integrating BV with the Android Bluetooth stack. It includes:
- Scripts for building the BV Dafny code and integrating it with the Android Bluetooth stack.
- Additional details for compiling the Bluetooth module with BV's Dafny code.

## Running verification scripts

To run the BV verification artifact, you can use either Dafny directly or via Docker.

### Option 1: Using Docker (Recommended)

If you have Docker installed, simply run the following command from the root of the BV directory:

```bash
$ docker build -t bv .
$ docker run --rm -v "$PWD":/app bv
```

### Option 2: Using Dafny Locally

If Dafny is installed on your machine, you can run:
```bash
$ dafny verify dfyconfig.toml
```

Expected output will indicate successful verification of the Dafny project, including all proofs and the state machine implementation.
```bash
Dafny program verifier finished with 229 verified, 0 errors
```

## Running Build Scripts

We provide a script that compiles our code with the rest of the Android Bluetooth stack and
generates shared libraries that can be deployed to an Android device. There are two shared libraries
we generate, a 32-bit version and a 64-bit version, and they are all named `libbluetooth.so`. We
also provide a script that deploys our shared libraries to an Android device. These scripts are
located under [`build/`](./build/). We also provide pre-built binaries for your
convenience.

**Note:** The build process is resource-intensive and may take a few hours to complete,
depending on your machine's specifications.

### Building

Please make sure you meet the following requirements before proceeding:
- Docker
- Bash
- Approximately 300 GB of storage

You can start the build process by running the following commands.

```console
$ cd build
build$ bash ./build.sh
```

Building the shared libraries is performed inside Docker and is persisted in a directory named
`work/` under the `build/` directory.

The following are the steps performed by [`build.sh`](./build/build.sh) to build the
shared libraries:

1. Building a Docker image for the build environment.

    It generates a Docker image customized for building Android (AOSP) and Dafny programs.

1. Creating a work directory.

    The script creates a work directory, which is used by Docker to hold the AOSP source code.

    It is used to make the build artifacts persistent. It is well-known that AOSP building is
    sensitive to network conditions and susceptible to failures. Therefore, making build artifacts
    persistent gives the user a chance to retry without losing the progress.

    Files created under this folder are owned by the containers. By default, other users only have
    read-only access to these files.

1. Cloning AOSP under the work directory.

    Following the instructions in the [official
    documents](https://source.android.com/docs/setup/download), this step involves downloading the
    source code using `repo`, and the propriety binaries for the target device. You will be prompted
    to provide additional information as required by these steps.
    For example, `repo` may ask you to provide your name and email address for git configurations,
    or propriety binary extraction asks you to agree to the terms of the license agreement. 

    As mentioned earlier, building AOSP is known to be sensitive to network conditions and
    susceptible to failures. Therefore, you may need to retry this step if failures occur.

    The source code is obtained based on our version of the manifest. This version uses our fork of
    the Bluetooth module and defaults to tag `android-12.1.0_r21`. Our fork of the Bluetooth module
    includes our source code and build files.

    For the propriety binaries, the script defaults to the image for Google Pixel 6 and Android
    12.1.0, which is used for our experiments. You can modify it in the [script
    file](./build/container/scripts/aosp_clone.sh).

1. Build our Bluetooth module.

    After successfully downloading the AOSP source, the build process is executed. This process
    starts with translating Dafny code into C++, and then building AOSP with our Bluetooth module.
    AOSP's build system puts the compiled binaries under `out/target/product/oriole(<device codename>)/system` directory,
    including the two target binaries, `lib/libbluetooth.so` (the 32-bit version)
    and `lib64/libbluetooth.so` (the 64-bit version).

### Deployment (Optional)

We also provide a script that deploys the generated shared libraries to an Android device. Since
deployment requires an Android device, this is not intended to be part of the artifact evaluation
submission. Rather, we provide it to interested reviewers to demonstrate that we can deploy and run
our Bluetooth stack on an Android device. The deployment is performed using the Android Debug Bridge
(ADB) tool, which is a command-line tool that allows you to communicate with an Android device.

```console
build$ bash ./deploy.sh
```

[`deploy.sh`](./build/deploy.sh) handles the deployment. If you have successfully performed
the build stage, the script starts a container and pushes the built binaries.

Otherwise, the script uses the [prebuilt binaries](./build/prebuilt). For this to
work, you need to have `adb` available in your environment.