from setuptools import setup
from setuptools.command.install import install as BaseInstall

setup(
    name='PyLambda_OG',
    version='0.0.1',
    install_requires=[
        'python_version>="3.8"',
    ],
    package_data={ 'PyLambda_OG': ['LambdaC/lambda.so'] },
)