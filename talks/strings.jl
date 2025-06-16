using Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics

import Convex, SCS
import TikzPictures
import Catlab.Graphics: TikZ

M = Ob(FreeAbelianBicategoryRelations, :M)

# TikZ.pprint(to_tikz(mcopy(M) ⋅ (mcopy(M)⊕mcopy(M)), orientation=BottomToTop, labels=true))
TikZ.pprint(to_tikz(mcopy(M) ⋅ (mcopy(M)⊕mcopy(M)) ⋅ (id(M) ⊕ swap(M, M) ⊕ id(M)), orientation=BottomToTop, labels=true))
