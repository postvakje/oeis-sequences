from setuptools import setup, find_packages

with open("README.md", "r") as fh:
    long_description = fh.read()
with open("requirements.txt", "r") as fh:
    requirements = [line.strip() for line in fh]

setup(
   name='OEISsequences',
   python_requires='>= 3.8',
   version='0.0.1',
   author='Chai Wah Wu',
   author_email='cwwuieee@gmail.com',
   packages=find_packages(),
   url='http://pypi.python.org/pypi/oeis-sequences/',
   license='LICENSE',
   description='Python functions to generate OEIS sequences',
   long_description=long_description,
   install_requires=requirements,
   classifiers = ['Programming Language :: Python :: 3',
                'License :: OSI Approved :: Apache Software License',
                'Operating System :: OS Independent',  
                'Topic :: Scientific/Engineering :: Mathematics',
                'Development Status :: 4 - Beta',
   ],
)