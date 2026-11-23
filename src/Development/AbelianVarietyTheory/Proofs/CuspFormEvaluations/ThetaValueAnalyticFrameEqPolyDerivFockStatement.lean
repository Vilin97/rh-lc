module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDerivStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExpNsmulEqPowVt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FockLaws

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem fock_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (q : ℤ) (a b : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) :
    fock Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Hm a b).im : ℂ)) *
      fock Hm q a (fock Hm q b θ) z := by
  have hl : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp [hermForm, add_dotProduct]
  have hr : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have hs : hermForm Hm b a = star (hermForm Hm a b) := by
    rw [hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
      Matrix.dotProduct_mulVec]
  have hsc : hermForm Hm b a = hermForm Hm a b - 2 * Complex.I * ((hermForm Hm a b).im : ℂ) := by
    rw [hs]
    apply Complex.ext <;> simp
    ring
  funext z
  simp only [fock]
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [hl, hr, hsc]
  ring

theorem fock_sq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    fock Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z) := by
  have h : ∀ z w, hermForm Hm ((N : ℂ) • z) ((N : ℂ) • w) = (N : ℂ) ^ 2 * hermForm Hm z w := fun z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      star_natCast]
    ring
  funext z
  simp only [fock, h, smul_add]
  congr 2
  push_cast
  ring

theorem fock_laws : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ (q : ℤ) (a b : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) * fock Φ.Hm q a (fock Φ.Hm q b θ) z) ∧ (∀ (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Φ.Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ ∀ θ, Φ.IsTh 1 θ → ∀ a ∈ Φ.lat, fock Φ.Hm 1 a θ = fun z => Φ.χ a * θ z := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun q a b θ => fock_add Φ.herm q a b θ, fun N a θ => fock_sq Φ.Hm N a θ, fun θ hθ a ha => ?_⟩
  funext z
  simp only [fock, hθ.2 a ha z, AnFr.fac, zpow_one]
  have : Complex.exp (-(((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm z a) - ((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm a a / 2) *
      Complex.exp (Real.pi * hermForm Φ.Hm z a + Real.pi / 2 * hermForm Φ.Hm a a) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (Φ.χ a * θ z) * this

end GlobalTheory.AnVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionAtLevelPointEqTranslateByRepresentative

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.VtLevel

theorem tyAct_natCast_mul {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ) (a : 𝓞 E)
    (z : Fin g → ℂ) : tyAct ty ((n : 𝓞 E) * a) z = (n : ℂ) • tyAct ty a z := by
  funext k
  simp [tyAct, _root_.mul_assoc]

theorem tyAct_natCast {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (n : ℕ)
    (z : Fin g → ℂ) : tyAct ty (n : 𝓞 E) z = (n : ℂ) • z := by
  funext k
  simp [tyAct]

theorem hermForm_smul_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

theorem hermForm_two_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z ((2 : ℂ) • w) = 2 * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

theorem hermForm_add_left' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem e_natCast_smul (n : ℕ) (z : Fin g → ℂ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero => simpa using (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem sub_mem_of_e_eq {z w : Fin g → ℂ} (h : Φ.e z = Φ.e w) : z - w ∈ Φ.lat := by
  rw [← Φ.e_ker]
  have h1 := Φ.e_add (z - w) w
  rw [sub_add_cancel, h] at h1
  exact (mul_eq_right.1 h1.symm)

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

theorem bar_mem {r : 𝓞 E} (hr : r ∈ Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) :
    ∃ α ∈ l.Mb ^ 2, H.bar r = ((2 : ℕ) : 𝓞 E) * α := by
  have h1 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hr
  have h2 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar a
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_map, h2, Ideal.map_id, Ideal.map_span, Set.image_singleton,
    map_ofNat, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨α, hα, h⟩ := h1
  exact ⟨α, hα, by rw [Nat.cast_ofNat, h]; rfl⟩

theorem smul_eq_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La))
    {α : 𝓞 E} (hα : α ∈ l.Mb ^ 2) : ∃ w : Dw.La, α • x2 = ((l.M ^ 2 : ℕ) : 𝓞 E) • w := by
  have h1 := Submodule.smul_mem_smul hα hx
  rw [← Submodule.mul_smul] at h1
  have h2 : l.Mb ^ 2 * (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) ≤
      Ideal.span {((l.M ^ 2 : ℕ) : 𝓞 E)} := by
    rw [mul_left_comm, ← mul_pow, l.prod, Ideal.span_singleton_pow, Nat.cast_pow]
    exact Ideal.mul_le_right
  have h3 := Submodule.smul_mono_left h2 h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, hw.symm⟩

theorem eq_two_smul_of_mem {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ w : Dw.La, x2 = w + w := by
  have h3 := Submodule.smul_mono_left (Ideal.mul_le_left) hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨w, -, hw⟩ := h3
  exact ⟨w, by rw [← hw, two_smul]⟩

variable {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem killedBy_iff (I : Ideal (𝓞 E)) (z : Fin g → ℂ) :
    KilledBy Xo I (Φ.e z) ↔ ∀ α ∈ I, tyAct ty α z ∈ Φ.lat := by
  refine forall₂_congr fun α _ => ?_
  rw [← Φ.lin, Φ.e_ker]

theorem levPt_eq {x x2 : Dw.La} (h : x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y.x x2 = levPt Xo y.x x := by
  have h1 := Xo.univ.eta_add (x2 - x) x
  rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
  unfold levPt
  rw [h1]

theorem im_even (mk : Dw.La →+ (Fin g → ℂ)) (hmk : ∀ a, mk a ∈ Φ.lat)
    (hlin : ∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) {u : Fin g → ℂ}
    (hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α u ∈ Φ.lat) {x2 : Dw.La}
    (hx : x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ k : ℤ, (hermForm Φ.Hm (mk x2) u).im = 2 * k := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr w _
    obtain ⟨α, hα, h⟩ := bar_mem hr
    obtain ⟨k, hk⟩ := ((anFr_semichar _ _ _ _ _ Φ.toAnFr).1 _ (hmk w) _ (hu α hα)).1
    refine ⟨k, ?_⟩
    rw [hlin, Φ.adj, h, tyAct_natCast_mul, Nat.cast_ofNat, hermForm_two_right, ← hk]
    simp
  · rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
    refine ⟨k + k', ?_⟩
    rw [map_add (f := _), hermForm_add_left', Complex.add_im, hk, hk']
    push_cast
    ring

end

end GlobalTheory.AnVal.VtLevel

open GlobalTheory.AnVal.VtLevel in
theorem GlobalTheory.AnVal.rd_vt_levPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ mk hmk hlin hlev θ hθ x x2 hx2 hx
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hk : ∀ α ∈ l.Mb ^ 2, tyAct ty α (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ∈ Φ.lat := by
    intro α hα
    obtain ⟨w, hw⟩ := smul_eq_of_mem hx2 hα
    rw [map_smul, ← hlin, hw, hlin, tyAct_natCast, smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM),
      one_smul]
    exact hmk w
  have hp : Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x := by
    have hm : x2 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono_left (Ideal.mul_le_right.trans (Ideal.pow_le_self two_ne_zero)) hx2
    rw [← levPt_eq hx, hlev x2 hm, ← e_natCast_smul, smul_smul]
    congr 2
    field_simp
  refine ⟨⟨(killedBy_iff Φ _ _).2 hk, hp⟩, fun F hF => ?_⟩
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha => (chi_eq_sign E H Dw l Xo c y g ty el Φ a ha).1
  have hMm : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
    rw [Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ 2
    refine (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) ?_
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨x', δ, hδ, h2, hok, hpow, hrd⟩ :=
    (rd_vt_and_uu _ _ _ _ _ Φ.toAnFr hχ l.M l.odd y.s θ hθ).1 _ _ F hF (by
      intro t' ht' _
      obtain ⟨z, rfl⟩ := Φ.e_onto t'
      have h1 := (killedBy_iff Φ _ _).1 ht' _ hMm
      rw [tyAct_natCast] at h1
      rw [← e_natCast_smul, Φ.e_ker]
      exact h1)
  set a : Fin g → ℂ := ((l.M : ℂ) ^ 2)⁻¹ • mk x2 with ha
  have hu : ∀ α ∈ l.Mb ^ 2, tyAct ty α (x' - a) ∈ Φ.lat := fun α hα => by
    rw [map_sub]
    exact Φ.lat.sub_mem ((killedBy_iff Φ _ _).1 hok α hα) (hk α hα)
  have hb : (l.M : ℂ) • (x' - a) ∈ Φ.lat := by
    rw [smul_sub]
    apply sub_mem_of_e_eq
    rw [e_natCast_smul, e_natCast_smul, hpow, hp]
  obtain ⟨w, hw⟩ := eq_two_smul_of_mem hx2
  obtain ⟨k, hk2⟩ := l.odd
  have hMa : ((l.M : ℂ) ^ 2) • a = mk w + mk w := by
    rw [ha, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul, hw, map_add (f := _)]
  have hb2 : (l.M : ℂ) • (x' - a) = (2 : ℂ) • (δ - mk w - k • ((l.M : ℂ) • (x' - a))) := by
    have h3 : (l.M : ℂ) • ((l.M : ℂ) • (x' - a)) = (2 : ℂ) • δ - (mk w + mk w) := by
      rw [smul_smul, ← sq, smul_sub, h2, hMa]
    generalize (l.M : ℂ) • (x' - a) = b at h3 ⊢
    rw [hk2] at h3
    funext i
    have := congrFun h3 i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    rw [nsmul_eq_mul]
    push_cast at this
    linear_combination this
  have hχb : Φ.χ ((l.M : ℂ) • (x' - a)) = 1 := by
    rw [hb2]
    exact (anFr_semichar _ _ _ _ _ Φ.toAnFr).2.2 hχ _
      (Φ.lat.sub_mem (Φ.lat.sub_mem hδ (hmk w)) (Φ.lat.nsmul_mem hb k))
  obtain ⟨f1, f2, f3⟩ := fock_laws _ _ _ _ _ Φ.toAnFr
  have hth := (reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 y.s).2.1 θ hθ
  obtain ⟨m, hm⟩ := im_even Φ mk hmk hlin hu hx2
  have hx' : x' = a + (x' - a) := by abel
  rw [hx', f1, f2 l.M (x' - a), f3 θ hth _ hb, hχb] at hrd
  have he : Complex.exp (((((l.M : ℤ) ^ 2 : ℤ) : ℂ)) * Real.pi * Complex.I *
      ((hermForm Φ.Hm a (x' - a)).im : ℂ)) = 1 := by
    have h4 : (hermForm Φ.Hm a (x' - a)).im = ((l.M : ℝ) ^ 2)⁻¹ * (2 * m) := by
      rw [← hm]
      nth_rewrite 1 [ha]
      rw [hermForm_smul_left', ← Complex.im_ofReal_mul]
      push_cast
      rfl
    rw [h4, ← Complex.exp_int_mul_two_pi_mul_I m]
    congr 1
    push_cast
    field_simp
  rw [he] at hrd
  simpa only [_root_.one_mul] using hrd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionAtLevelPointEqTranslateByRepresentativeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_at_level_point_eq_translate_by_representative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ x x2 : Dw.La, x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) → x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) → (KilledBy Xo (l.Mb ^ 2) (Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2)) ∧ Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk x2) ^ l.M = levPt Xo y.x x) ∧ ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)), IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F → Φ.toAnFr.Rd ((l.M : ℤ) ^ 2) F (fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk x2) fun z => θ ((l.M : ℂ) • z)) := by
  first | exact @GlobalTheory.AnVal.rd_vt_levPt | exact GlobalTheory.AnVal.rd_vt_levPt | (intros; apply GlobalTheory.AnVal.rd_vt_levPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueAnalyticFrameEqPolyDerivFock

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.e_natCast_smul_eq_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e ((n : ℂ) • z) = Φ.e z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem thValAt_eq_polyDeriv_fock : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v : ℂ, ThValAt Xo c nab y x P v → v = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) (fun w => θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ mk hlat hlin hlev nab hnab θ hθ n x x2 hx2 hx a P hP v hv
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.odd.pos.ne'
  have hV := fun b => GlobalTheory.T.section_at_level_point_eq_translate_by_representative E H Dw l Xo c y g ty el Φ mk hlat hlin hlev θ hθ (x b) (x2 b) (hx2 b) (hx b)
  have hpow : ∀ b, Φ.e (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) ^ (l.M ^ 2) = 1 := by
    intro b
    rw [← Φ.toAnFr.e_natCast_smul_eq_pow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero 2 hM), one_smul]
    exact (Φ.e_ker _).2 (hlat _)
  have hex := fun b => (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1
    (KilledBy Xo (l.Mb ^ 2)) (levPt Xo y.x (x b)) _ (hV b).1.2 (hpow b) (hV b).1.1
  choose F hF using hex
  have hw : ThValAt Xo c nab y x P (thExpr Xo c nab y P F) :=
    ⟨ℂ, inferInstance, inferInstance, AlgHom.id c.F ℂ, y, F,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hF, rfl⟩
  have hvw : v = thExpr Xo c nab y P F :=
    GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hnab ℂ ℂ (AlgHom.id c.F ℂ) y y
      (GlobalTheory.FramedBaseChange.refl y) a n x P hP v _ hv hw
  have hN := GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv hC E H Dw l Xo c y g ty el Φ nab hnab (l.M ^ 2) n F _
    (fun b => (hV b).2 (F b) (hF b)) a P hP.1
  rw [hvw, thExpr, map_inv₀, map_pow, map_natCast, ← inv_pow]
  exact congrArg _ hN

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueAnalyticFrameEqPolyDerivFockStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaValue_analyticFrame_eq_polyDeriv_fock : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v : ℂ, ThValAt Xo c nab y x P v → v = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) (fun w => θ ((l.M : ℂ) • w)) (z b)) 0 := by
  first | exact @GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock | exact GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock | (intros; apply GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock <;> assumption)
end
end
