import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

end TsenCount

open Polynomial TsenCount in

end GlobalTheory
