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

# Build both the library and the executable
RUN lake build
RUN lake build gungnir_operator

# Runtime stage -- minimal image
FROM ubuntu:24.04

RUN apt-get update && apt-get install -y \
    ca-certificates \
    curl \
    netcat-openbsd \
    && curl -Lo /usr/local/bin/kubectl \
       "https://dl.k8s.io/release/$(curl -Ls https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl" \
    && chmod +x /usr/local/bin/kubectl \
    && apt-get remove -y curl \
    && apt-get autoremove -y \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/.lake/build/bin/gungnir_operator /usr/local/bin/

USER 65534:65534
ENTRYPOINT ["/usr/local/bin/gungnir_operator"]
