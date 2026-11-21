import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def jC {R W V : Type} [CommRing R] [CommRing W] [CommRing V] (φ : R →+* W) (g : W →+* V) :
    Over.mk (spMap (g.comp φ)) ⟶ Over.mk (spMap φ) :=
  Over.homMk (spMap g) (by
    show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (g.comp φ))
    rw [← Spec.map_comp]; rfl)

section
variable {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ} {T T' : Over S} {h : T' ⟶ T} {n : ℕ}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c : Fin n → Γ(T'.left, ⊤)} {s : LB.Sec (LPow G L (N : ℤ) T')}

end

open GlobalTheory.FramePull in

open GlobalTheory.FramePull in

end GlobalTheory.TorRef
