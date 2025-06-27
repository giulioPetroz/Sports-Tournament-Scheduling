FROM ubuntu:latest
FROM minizinc/minizinc:2.9.1-jammy

WORKDIR /cdmo

# Install basic dependencies (curl for miniconda installer)
RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y curl bzip2 git && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Install Miniconda
ENV CONDA_DIR=/opt/conda
RUN curl -LO "https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh" && \
    bash Miniconda3-latest-Linux-x86_64.sh -b -p $CONDA_DIR && \
    rm Miniconda3-latest-Linux-x86_64.sh && \
    $CONDA_DIR/bin/conda clean --all --yes

# Add Conda to PATH
ENV PATH=$CONDA_DIR/bin:$PATH

# Copy environment.yml file into the container
COPY environment.yml .

# Create the Conda environment
RUN conda env create -f environment.yml && \
    conda clean --all --yes

# Activate the environment for subsequent commands
ENV CONDA_DEFAULT_ENV=CDMO
ENV PATH="$CONDA_DIR/envs/${CONDA_DEFAULT_ENV}/bin:$PATH"

# Copy project files
COPY . .

CMD ["bash"]