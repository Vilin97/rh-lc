import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Φ : FlagCpt Z e)

private theorem log_valuation_mul {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) (y : AlgPt Y) {f g : Y.Fn}
    (hf : UnitAt (below y.1) f) (hg : UnitAt (below y.1) g) :
    Real.log (ε.w (valAt y.1 (f * g))) = Real.log (ε.w (valAt y.1 f)) + Real.log (ε.w (valAt y.1 g)) := by
  rw [SmallSec.valAt_mul hf.regAt hg.regAt, map_mul,
    Real.log_mul (ε.w.ne_zero (SmallSec.valAt_ne_zero hf)) (ε.w.ne_zero (SmallSec.valAt_ne_zero hg))]

omit [NumberField F] in
private theorem isEqn_prod (n : Letter Dw → ℤ) (y : Φ.Y.X) :
    (divOf Φ n).IsEqn y (∏ x : Letter Dw, LineNorm.dg Φ y x.1 x.2 ^ n x) :=
  LineNorm.isEqn_sum _ y fun x => ((LineNorm.fr_spec Φ y).2 x.1 x.2).zsmul (n x)

private theorem lam_eq {C : CxSt F} (hm : Mets Φ C) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Φ.Y) (h : (divOf Φ (expo Dw w)).IsEqn (below y.1) 1) :
    lam (adlOf Φ hm w) v ε y = Real.log (ε.w (valAt y.1
      ((∏ x : Letter Dw, LineNorm.dg Φ (below y.1) x.1 x.2 ^ expo Dw w x : Φ.Y.Fnˣ) : Φ.Y.Fn))) +
      ∑ a ∈ w.support, (w a : ℝ) * LineNorm.symLog Φ a.1 a.2.2 v ε y := by
  have hq : (divOf Φ (expo Dw w)).IsEqn (below y.1) (eqn (divOf Φ (expo Dw w)) (below y.1)) :=
    (CartierDiv.exists_isEqn _ _).choose_spec
  have u₁ : UnitAt (below y.1) (((∏ x : Letter Dw, LineNorm.dg Φ (below y.1) x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Φ (expo Dw w)) (below y.1))⁻¹ : Φ.Y.Fnˣ) : Φ.Y.Fn) := by
    have := hq.iff_unitAt.1 (isEqn_prod Φ (expo Dw w) (below y.1))
    rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  have u₂ : UnitAt (below y.1) (eqn (divOf Φ (expo Dw w)) (below y.1) : Φ.Y.Fn) := by
    have := h.iff_unitAt.1 hq
    rwa [Units.val_one, div_one] at this
  have e₀ : lam (adlOf Φ hm w) v ε y = LineNorm.lgCopy Φ w v ε y +
      Real.log (ε.w (valAt y.1 (eqn (divOf Φ (expo Dw w)) (below y.1) : Φ.Y.Fn))) := rfl
  have e₁ := log_valuation_mul ε y u₁ u₂
  rw [← Units.val_mul, inv_mul_cancel_right] at e₁
  rw [e₀, LineNorm.lgCopy_eq, e₁]
  ring

end SlopeTestRemainingChoices
