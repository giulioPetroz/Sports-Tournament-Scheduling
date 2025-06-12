# To build docker image from dockerfile:

    `docker build -t cdmo .`

# To run container:

    `docker run -it cdmo`

Close container:

    `exit`

## To run container with the CPLEX solver:
- ensure CPLEX is installed on device, it will be mounted at runtime
- run container with:

    `sudo docker run -v /user/path/to/cplex:/opt/ibm/ILOG/ -v $(pwd):/cdmo -w /cdmo -it cdmo`
    
    - sudo might be required to allow docker to access CPLEX's folder
    - Usage example: `sudo docker run -v /opt/ibm/ILOG/:/opt/ibm/ILOG/ -v $(pwd):/cdmo -w /cdmo cdmo`
