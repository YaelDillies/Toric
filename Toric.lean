import Toric.Examples.CharCocharPairing
import Toric.Examples.SO2
import Toric.GroupScheme.Character
import Toric.GroupScheme.Diagonalizable
import Toric.GroupScheme.HopfAffine
import Toric.GroupScheme.MonoidAlgebra
import Toric.GroupScheme.Torus
import Toric.Hopf.Diagonalisable
import Toric.Hopf.GrpAlg
import Toric.Hopf.MonoidAlgebra
import Toric.Mathlib.Algebra.AffineMonoid.Embedding
import Toric.Mathlib.Algebra.AffineMonoid.Irreducible
import Toric.Mathlib.Algebra.AffineMonoid.UniqueSums
import Toric.Mathlib.Algebra.Algebra.Defs
import Toric.Mathlib.Algebra.Algebra.Equiv
import Toric.Mathlib.Algebra.Algebra.Hom
import Toric.Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Toric.Mathlib.Algebra.Category.CommBialgCat
import Toric.Mathlib.Algebra.Category.CommHopfAlgCat
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Toric.Mathlib.Algebra.Category.MonCat.Basic
import Toric.Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Toric.Mathlib.Algebra.Group.Equiv.Basic
import Toric.Mathlib.Algebra.Group.Finsupp
import Toric.Mathlib.Algebra.Group.TypeTags.Hom
import Toric.Mathlib.Algebra.Group.Units.Hom
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.Mathlib.Algebra.MonoidAlgebra.MapDomain
import Toric.Mathlib.Algebra.Polynomial.AlgebraMap
import Toric.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Toric.Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.AlgebraicGeometry.Scheme
import Toric.Mathlib.CategoryTheory.Comma.Over.Basic
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass
import Toric.Mathlib.CategoryTheory.Functor.FullyFaithful
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Toric.Mathlib.CategoryTheory.Monoidal.Attr
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Toric.Mathlib.CategoryTheory.Monoidal.Category
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Mod_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.Data.Finsupp.Single
import Toric.Mathlib.Geometry.Convex.Cone.Dual
import Toric.Mathlib.Geometry.Convex.Cone.Pointed
import Toric.Mathlib.Geometry.Convex.Cone.Polyhedral
import Toric.Mathlib.Geometry.Convex.Polytope
import Toric.Mathlib.GroupTheory.FreeAbelianGroup
import Toric.Mathlib.GroupTheory.FreeGroup.Basic
import Toric.Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Toric.Mathlib.LinearAlgebra.PerfectPairing.Basic
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.LinearAlgebra.UnitaryGroup
import Toric.Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.Bialgebra.Convolution
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.RingTheory.Bialgebra.GroupLike
import Toric.Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Bialgebra.TensorProduct
import Toric.Mathlib.RingTheory.Coalgebra.CoassocSimps
import Toric.Mathlib.RingTheory.Coalgebra.Convolution
import Toric.Mathlib.RingTheory.Coalgebra.GroupLike
import Toric.Mathlib.RingTheory.Coalgebra.Hom
import Toric.Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Coalgebra.SimpAttr
import Toric.Mathlib.RingTheory.FiniteType
import Toric.Mathlib.RingTheory.Finiteness.Finsupp
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.HopfAlgebra.Convolution
import Toric.Mathlib.RingTheory.HopfAlgebra.GroupLike
import Toric.Mathlib.RingTheory.HopfAlgebra.Hom
import Toric.Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Toric.Mathlib.RingTheory.TensorProduct.Basic
import Toric.MonoidAlgebra.TensorProduct
import Toric.MvLaurentPolynomial
import Toric.SphericalVariety
import Toric.ToricIdeal
import Toric.ToricVariety.Defs
import Toric.ToricVariety.FromMonoid
import Toric.Util.TrackSorry
