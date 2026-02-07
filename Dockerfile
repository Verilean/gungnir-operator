FROM ubuntu:24.04 AS builder

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl git cmake gcc g++ make \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean toolchain manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Copy project files
WORKDIR /app
COPY lean-toolchain .
COPY lakefile.lean .

# Install the correct Lean toolchain
RUN elan install $(cat lean-toolchain | tr -d '\n')
RUN lake update

# Copy source code
COPY Gungnir/ Gungnir/

# Build the project
RUN lake build
