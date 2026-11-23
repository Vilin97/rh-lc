module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreMatching
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RatPt

variable {D : D7} {S T : HSp D}

theorem exists_fin_add_real (w : WO S T) :
    ∃ u v : WO S T, u.map (infPart D) = 0 ∧ v.map (finPart D) = 0 ∧ w = u + v := by
  let e : AE D := (pairA D.host.F 1 0) ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D e = 1 := rfl
  have h0 : finPart D e = 0 := by
    change (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  refine ⟨Matrix.of fun i j => (1 - e) * w i j, Matrix.of fun i j => e * w i j, ?_, ?_, ?_⟩
  · ext i j
    change infPart D ((1 - e) * w i j) = 0
    rw [RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, sub_self, zero_mul]
  · ext i j
    change finPart D (e * w i j) = 0
    rw [RingHom.map_mul, h0, zero_mul]
  · ext i j
    change w i j = (1 - e) * w i j + e * w i j
    rw [← add_mul, sub_add_cancel, one_mul]

theorem isTheta_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) : IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h : IsThetaFunO ψ S T (heisO ψ S T u (heisO ψ S T v f)) := by
    simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1
      (heisO ψ S T v f) (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf)
      Unit Finset.univ (fun _ => u) (fun _ => 1) (by intro i hi; exact hu)
  rw [GlobalTheory.WeilVacMove.heisO_heisO, (GlobalTheory.WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h
  exact h

theorem actO_one (h : GA D T) (w : WO S T) : actO S T 1 h w =
    HMul.hMul (Formalism.L2.Theta.mt T h) (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  rw [inv_one, GlobalTheory.Ker.OmRat.mt_one', Matrix.mul_one]

theorem compAt_mul (θ : InfFam D) (ρ : D.what₂.Tau) {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) :
    compAt θ ρ (x * y : Mx D a c) = compAt θ ρ x * compAt θ ρ y :=
  Matrix.map_mul (f := (θ ρ).comp (infPart D))

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {a b : ℕ}
    (m : Matrix (Fin a) (Fin b) D.host.E) : compAt θ ρ (m.map (incA D)) = m.map (tauE D ρ) := by
  ext i j
  exact (hθ ρ).1 (m i j)

theorem rational_points : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ δ ∈ GQ T, ∃ ga : GL (Fin r) D.host.E, Formalism.L2.Theta.mt T δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) ∧ IsUn X ga ∧ (∀ Z : Fam T, lact ga (frOf hr eT Z) = frOf hr eT (mvZ θ δ Z)) ∧ (∀ w : WO S T, (GlobalTheory.Ker.IsRealPt w → ∃ w' : WO S T, GlobalTheory.Ker.IsRealPt w' ∧ w = actO S T 1 δ w') ∧ ∀ τ k, rePt θ hr eT (actO S T 1 δ w) τ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ rePt θ hr eT w τ k) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ w, om (1, δ) f (actO S T 1 δ w) = f w := by
  intro D S T r g hr ψ θ X eT bas idx hS δ hδ
  subst hr
  obtain ⟨hψ, hθ, -, -, hM, -, he, -⟩ := hS
  obtain ⟨ga, hga, hδ'⟩ := id hδ
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have hc : ∀ τ : X.Ψ, compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) =
      (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 := fun τ => by
    rw [hm, compAt_rat hθ, ← he, Equiv.apply_symm_apply]
  refine ⟨ga, hm, ?_, fun Z => ?_, fun w => ⟨fun hw => ⟨actO S T 1 δ⁻¹ w, ?_, ?_⟩, fun τ k => ?_⟩, ?_⟩
  · intro x y
    have hG : X.Gm = (-T.gram)ᵀ := hM.1
    rw [hG, GlobalTheory.Ker.Grp.herm_eq, GlobalTheory.Ker.Grp.herm_eq]
    refine GlobalTheory.Ker.Grp.hform_mulVec _ _ _ ?_ _ _
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ga.1 * T.gram * ga.1 = T.gram := hga
    rw [Matrix.mul_neg, Matrix.neg_mul, h]
  · funext τ
    change (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 * Z (eT.symm τ) =
      compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) * Z (eT.symm τ)
    rw [hc]
  · unfold GlobalTheory.Ker.IsRealPt at hw ⊢
    rw [GlobalTheory.KerReal.map_actO, hw, Matrix.mul_zero, Matrix.zero_mul]
  · have := GlobalTheory.Ker.OmRat.actO_inv_cancel (1 : GA D S) δ w
    rw [inv_one] at this
    exact this.symm
  · funext a
    change compAt θ (eT.symm τ) (actO S T 1 δ w) a k = _
    rw [actO_one, compAt_mul, hc]
    rfl
  · intro χS χT om H f hf w
    have h1 := H.om_heis 1 δ w f hf
    have h2 := H.om_aut 1 (one_mem _) δ hδ _ (isTheta_heisO hψ hf w)
    rw [← GlobalTheory.Ker.OmRat.heisO_at_zero ψ _ (om (1, δ) f), ← h1]
    exact h2.trans (GlobalTheory.Ker.OmRat.heisO_at_zero _ _ _)

end GlobalTheory.OneMapRef.RatPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormHeckeEigen

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Equivar


open CategoryTheory MonObj in
theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

variable {D : D7} {S T : HSp D} {r g g' : ℕ}

theorem latW_injective (hr : T.rank = r) : Function.Injective (latW (D := D) (T := T) hr) := by
  subst hr
  intro L L' h
  ext v
  exact SetLike.ext_iff.1 h v

theorem sameSp_of_isSet {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} (h : IsSet ψ θ S T hr X eT bas) (h' : IsSet ψ θ S T hr X' eT' bas')
    (hp : X'.p0 = X.p0) : SameSp X' X := by
  obtain ⟨-, -, -, -, hm, hk, he, -⟩ := h
  obtain ⟨-, -, -, -, hm', hk', he', -⟩ := h'
  refine ⟨?_, hm'.1.trans hm.1.symm, hp, hm'.2.trans hm.2.symm, hk'.trans hk.symm⟩
  ext τ
  constructor
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT'.surjective ⟨τ, hτ⟩
    have : τ = (eT ρ).1 := by rw [he, ← he', hρ]
    exact this ▸ (eT ρ).2
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT.surjective ⟨τ, hτ⟩
    have : τ = (eT' ρ).1 := by rw [he', ← he, hρ]
    exact this ▸ (eT' ρ).2

theorem symm_eq_of_isSet {X X' : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ}
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) (he' : ∀ ρ, (eT' ρ).1 = tauE D ρ) (τ : D.host.E →+* ℂ) (h : τ ∈ X.Ψ)
    (h' : τ ∈ X'.Ψ) : eT'.symm ⟨τ, h'⟩ = eT.symm ⟨τ, h⟩ := by
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [he', ← he, Equiv.apply_symm_apply]

theorem exists_real_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (h : IsSet ψ θ S T hr X eT bas)
    (idx : Fin g ≃ X.Ψ × Fin r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {L : Lt D.host.E r} {th : (Fin g → ℂ) → ℂ}
    (hm : MeanOne X bas idx x L th) : ∃ w : WO S T, Ker.IsRealPt w ∧
      Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) * ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b) ≠ 0 := by
  obtain ⟨-, hθ, -, hev, -, -, -, hs⟩ := h
  obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨_, _, -, -, h3⟩ := hm
    simp [hc] at h3
  have hq : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  obtain ⟨⟨Lz, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws _ r X g _ hq bas idx S.rank hs hev x hx
  obtain ⟨v, hv⟩ := Lz.surjective fun _ => z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hw : rePt θ hr eT (Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a) : WO S T) = v := by
    funext τ k a
    have := hσ.comp (fun ρ => v (eT ρ) k (Fin.cast hr (Fin.cast hr.symm a))) (eT.symm τ)
    refine this.trans ?_
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a), Matrix.ext fun a k => hσ.fin _, ?_⟩
  rw [hw, ← hL, hv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun _ _ => hz)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem compare {σ : c.F →+* ℂ} (hA : l.A = 1) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : LatEmb T ι) {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {e' : Fin g' ≃ Lt1 Dw} (hS : IsSet ψ θ S T hr X eT bas) (hS' : IsSet ψ θ S T hr X' eT' bas')
    (hM : Matched c σ X idx e) (hM' : Matched c σ X' idx' e') (hp : X'.p0 = X.p0) (hD : SelfD X X.Λ)
    (hD' : SelfD X' X'.Λ) {δ a' : GA D T} (hδ : δ ∈ GQ T) (hL : latW hr X.Λ = latG T (δ * a'))
    (hL' : latW hr X'.Λ = latG T a') {Z : Fam T} (hZ : IsONeg T X.p0 Z) {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}
    (hx : x ∈ X.dom) (hx' : x' ∈ X'.dom) (ex : x = frOf hr eT (mvZ θ (δ * a') Z)) (ex' : x' = frOf hr eT' (mvZ θ a' Z)) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x X.Λ y) (A' : AnFib X' bas' idx' e' x' X'.Λ y')
      (th : (Fin g → ℂ) → ℂ) (th' : (Fin g' → ℂ) → ℂ), A.Reads 1 y.s th → A'.Reads 1 y'.s th' →
      ∀ mk mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ X.Λ) → (∀ a, mk' a ∈ X'.Λ) →
      MarkAd hr l ι (δ * a') mk → MarkAd hr l ι a' mk' → A.Marked mk → A'.Marked mk' →
      ∃ lam : ℂ, (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y) ∧
        ∀ w : WO S T, Ker.IsRealPt w → ∃ w' : WO S T, Ker.IsRealPt w' ∧
          Ker.gaussR X' bas' idx' x' (Ker.zR X' idx' x' (rePt θ hr eT' w')) *
              ∏ b, th' (Ker.zR X' idx' x' (rePt θ hr eT' w') b) =
            lam ^ S.rank * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b)) ∧
          ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
            IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → om (1, δ * a') f w = om (1, a') f w' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' A A' th th' hth hth' mk mk' hmk hmk' hm hm' hAm hAm'
  have hX : SameSp X' X := sameSp_of_isSet hS hS' hp
  have hsy := symm_eq_of_isSet hS.2.2.2.2.2.2.1 hS'.2.2.2.2.2.2.1
  obtain ⟨ga, g1, g2, g3, g4, g5⟩ := GlobalTheory.OneMapRef.RatPt.rational_points D S T r g hr ψ θ X eT bas idx hS δ hδ
  obtain ⟨k1, k2⟩ := ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι a' X'.Λ hL' l).2 mk' hmk' hm').2.2.2 δ ga g1
  have eL : mapL ga X'.Λ = X.Λ := latW_injective hr (k1.trans hL.symm)
  have eX : lact ga (castFr hX.psi x') = x := by
    have : castFr hX.psi x' = frOf hr eT (mvZ θ a' Z) := by
      rw [ex']
      funext τ a b
      simp only [castFr, frOf]
      rw [hsy τ.1 τ.2]
    rw [this, g3, ex, ((GlobalTheory.OneMapRef.oneg_frames D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 a').2.2.1 δ]
  have key := GlobalTheory.OneMapRef.anFib_move_renum D H Dw l Xo c σ r g g' X' X hX bas' idx' e' bas idx e hS'.2.2.2.2.2.2.2
    hS.2.2.2.2.2.2.2 hM' hM x' hx' X'.Λ hD' ga g2 y' A' th' hth'
  rw [eL, eX] at key
  obtain ⟨A₁, th₁, r1, r2, r3⟩ := key
  have hmem : ∀ a, mvMap ga mk' a ∈ X.Λ := fun a => eL ▸ ⟨mk' a, hmk' a, rfl⟩
  obtain ⟨m1, -, m3, -⟩ := (GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmem k2
  obtain ⟨lam, -, l2, l3⟩ := GlobalTheory.OneMapRef.exists_scalar_of_marked _ H Dw l Xo c r g X bas idx e x X.Λ hS.2.2.2.2.2.2.2 hx hD
    hA y y' A A₁ mk ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmk hm).1 hAm
    (marked_congr A₁ (r2 mk' hAm') (m3 l dvd_rfl le_rfl mk hmk hm)) th th₁ hth r1
  refine ⟨lam, l3, fun w hw => ?_⟩
  obtain ⟨w', hw', rfl⟩ := (g4 w).1 hw
  refine ⟨w', hw', ?_, fun χS χT om ho f hf => ?_⟩
  · rw [← r3 S.rank (rePt θ hr eT' w') (rePt θ hr eT (actO S T 1 δ w')), l2]
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    · intro τ k
      rw [(g4 w').2]
      congr 1
      funext a
      change compAt θ (eT.symm ⟨τ.1, hX.psi ▸ τ.2⟩) w' (Fin.cast hr.symm a) k =
        compAt θ (eT'.symm τ) w' (Fin.cast hr.symm a) k
      rw [hsy τ.1 (hX.psi ▸ τ.2) τ.2]
  · have : ((1, δ * a') : GA D S × GA D T) = (1, δ) * (1, a') := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply]
    exact g5 χS χT om ho _ (ho.om_pres _ _ hf) w'

theorem rdU_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (hx : x ∈ (U.X k).dom) : rdU U f k x = @evR _ _ _ _ _ _ _ Xo c f ℂ _ σ.toAlgebra (ptC U k ⟨x, hx⟩) :=
  dif_pos hx

end GlobalTheory.OneMapRef.Equivar
end
end
