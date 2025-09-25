# import speedscope

from spack.concretize import concretize_one
from spack.spec import Spec

# with speedscope.track('spack.py-speedscope.json'):
#     concretize_one(Spec('icu4c cxxstd=17'))

print(concretize_one(Spec('icu4c cxxstd=17')))
