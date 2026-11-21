import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (DVR.th D₀ (T := T) y J) := isCub_cubV D₀.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
