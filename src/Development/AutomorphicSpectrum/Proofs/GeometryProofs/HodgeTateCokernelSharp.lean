module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowersStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpA

section

@[expose] public section

noncomputable section

open TensorProduct Coalgebra WithConv GlobalTheory.GroupLikeDerivation

namespace PositivityTheory.HtPt.Farsharp

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {O : Type} [CommRing O] [Algebra O C] (hO : ∀ o : O, ‖algebraMap O C o‖ ≤ 1)
  {M : Type} [AddCommGroup M] [Module O M]


include hO in
theorem norm_le_of_mem_span (f : M →ₗ[O] C) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span O s) : ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx =>
    rw [map_smul, Algebra.smul_def, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hO o)).trans hx


include hO in
theorem bddAbove_norm [Module.Finite O M] (f : M →ₗ[O] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span hO f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supN (f : WithConv (M →ₗ[O] C)) : ℝ := ⨆ m, ‖f.ofConv m‖


include hO in
theorem le_supN [Module.Finite O M] (f : WithConv (M →ₗ[O] C)) (m : M) :
    ‖f.ofConv m‖ ≤ supN f := le_ciSup (bddAbove_norm hO f.ofConv) m


omit [IsUltrametricDist C] in
theorem supN_le {f : WithConv (M →ₗ[O] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supN f ≤ r := ciSup_le h


omit [IsUltrametricDist C] in
theorem supN_nonneg (f : WithConv (M →ₗ[O] C)) : 0 ≤ supN f :=
  Real.iSup_nonneg fun _ => norm_nonneg _


omit [IsUltrametricDist C] in
theorem supN_smul (c : C) (f : WithConv (M →ₗ[O] C)) :
    supN (c • f) = ‖c‖ * supN f := by
  rw [supN, supN, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl


include hO in
theorem supN_add_le [Module.Finite O M] (f g : WithConv (M →ₗ[O] C)) :
    supN (f + g) ≤ max (supN f) (supN g) :=
  supN_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supN hO f m) (le_supN hO g m))


include hO in
theorem supN_mul_le [Module.Finite O M] [Coalgebra O M]
    (f g : WithConv (M →ₗ[O] C)) : supN (f * g) ≤ supN f * supN g := by
  refine supN_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary O m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)

theorem supN_le_of_tmul {f : WithConv (M ⊗[O] M →ₗ[O] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supN f ≤ r := by
  refine supN_le fun t => ?_
  induction t with
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)


include hO in
theorem supN_eq_mul [Module.Finite O M] (f g : WithConv (M →ₗ[O] C))
    (h : WithConv (M ⊗[O] M →ₗ[O] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supN h = supN f * supN g := by
  apply le_antisymm
  · refine supN_le_of_tmul (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)
  · rw [supN.eq_1 f, Real.iSup_mul_of_nonneg (supN_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supN.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supN hO h _


include hO in
theorem exists_supN_pow_le [Module.Finite O M] [Coalgebra O M]
    [IsCocomm O M] {y : WithConv (M →ₗ[O] C)} (hy : IsIntegral O y) :
    ∃ K : ℝ, ∀ k : ℕ, supN (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supN f, fun k => supN_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span O (s : Set (WithConv (M →ₗ[O] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[O] C) →ₗ[O] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span hO ev (Finset.sum_nonneg fun _ _ => supN_nonneg _)
    (fun f hf => (le_supN hO f m).trans
      (Finset.single_le_sum (f := fun f => supN f) (fun _ _ => supN_nonneg _) hf)) hk

end Norm

theorem dvd_mul_of_norm (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (O : Type) [CommRing O] [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hO : ∀ x : C, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O C).range)
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : ‖algebraMap O C c‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  have hO' : ∀ o : O, ‖algebraMap O C o‖ ≤ 1 := fun o => (hO _).2 ⟨o, rfl⟩
  have hq' : algebraMap O C q ≠ 0 := fun h => hq (hinj (by rw [h, map_zero]))
  have hdvd : ∀ x : O, q ∣ x ↔ ‖(algebraMap O C q)⁻¹ * algebraMap O C x‖ ≤ 1 := fun x => by
    constructor
    · rintro ⟨z, rfl⟩
      rw [map_mul, inv_mul_cancel_left₀ hq']
      exact hO' z
    · intro h
      obtain ⟨z, hz⟩ := (hO _).1 h
      refine ⟨z, hinj ?_⟩
      rw [map_mul, hz, mul_inv_cancel_left₀ hq']
  set y : WithConv (A →ₗ[O] C) := (algebraMap O C q)⁻¹ • extendHom O C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (algebraMap O C q)⁻¹ * algebraMap O C (D a) := fun _ => rfl
  have : IsScalarTower O C (WithConv (A →ₗ[O] C)) := ⟨fun o x f =>
    WithConv.ext (LinearMap.ext fun a => smul_assoc o x (f.ofConv a))⟩
  have hint : IsIntegral O y :=
    GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed (B₀ := GlobalTheory.CartierDual O A) hinj hcl
      (extendHom O C A) (toConv D) q hq fun χ => by
        obtain ⟨u, h1, h2⟩ := exists_isGroupLikeElem χ
        rw [← h2]
        exact hu u h1
  have key := GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers C p hp _ _ supN supN (mulHom O C A)
    (inlHom O C A) (inrHom O C A) supN_smul supN_smul supN_nonneg
    supN_nonneg (supN_add_le hO') (supN_mul_le hO')
    (fun f => supN_le fun t => le_supN hO' f _)
    (fun f g => supN_eq_mul hO' f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supN_pow_le hO' hint)
    (supN_le_of_tmul zero_le_one fun a b => by
      have h := (hdvd _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      simp only [map_sub, map_mul]
      ring)
    (algebraMap O C c) hc
  rw [hdvd]
  have h : (algebraMap O C q)⁻¹ * algebraMap O C (c * D a) = (algebraMap O C c • y).ofConv a := by
    change _ = algebraMap O C c * y.ofConv a
    rw [hya, map_mul]
    ring
  rw [h]
  exact (le_supN hO' _ a).trans key

def powAbs {C : Type} [Field C] (v : Valuation C NNReal) (s : ℝ) (hs : 0 < s) : AbsoluteValue C ℝ where
  toFun x := ((v x : NNReal) : ℝ) ^ s
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  nonneg' x := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (NNReal.coe_nonneg _) hs.ne']
    simp
  add_le' x y := by
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem dvd_mul_of_val (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    (hp : v (p : C) < 1)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : v (algebraMap O C c) ^ (p - 1) ≤ v (p : C)) (a : A) :
    q ∣ c * D a := by
  have hpp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) < ((v (p : C) : NNReal) : ℝ) := by
    have : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
    exact NNReal.coe_pos.2 ((Valuation.pos_iff v).2 this)
  have hlog : Real.log ((v (p : C) : NNReal) : ℝ) < 0 := Real.log_neg hp0 (by exact_mod_cast hp)
  let s : ℝ := Real.log p / (-Real.log ((v (p : C) : NNReal) : ℝ))
  have hs : 0 < s := div_pos (Real.log_pos hp1) (neg_pos.2 hlog)
  letI : NormedField C := (powAbs v s hs).toNormedField
  have hn : ∀ x : C, ‖x‖ = ((v x : NNReal) : ℝ) ^ s := fun _ => rfl
  have hpn : ‖(p : C)‖ = (p : ℝ)⁻¹ := by
    rw [hn, Real.rpow_def_of_pos hp0]
    have : Real.log ((v (p : C) : NNReal) : ℝ) * s = -Real.log p := by
      have := hlog.ne
      simp only [s]
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by linarith)]
  letI : NontriviallyNormedField C :=
    { non_trivial := ⟨(p : C)⁻¹, by rw [norm_inv, hpn, inv_inv]; exact hp1⟩ }
  haveI : IsUltrametricDist C := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    fun x y => by
      rw [hn, hn, hn]
      rcases le_max_iff.1 (v.map_add x y) with h | h
      · exact le_max_of_le_left
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
      · exact le_max_of_le_right
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
  refine dvd_mul_of_norm C p hpn O hv.hom_inj (fun x => ?_)
    (fun z hz => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hz)) A q hq D hD hu c ?_ a
  · rw [hn]
    constructor
    · intro h
      refine hv.exists_of_le_one ?_
      by_contra h1
      exact absurd h (not_le.2 (Real.one_lt_rpow (by exact_mod_cast not_le.1 h1) hs))
    · rintro ⟨o, rfl⟩
      exact Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast hv.map_le_one o) hs.le
  · have h1 : ‖algebraMap O C c‖ ^ (p - 1) ≤ (p : ℝ)⁻¹ := by
      rw [← hpn, ← norm_pow, hn, hn, map_pow]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 hc) hs.le
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h3 : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    have h4 := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) h1 (one_div_pos.2 h2).le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h3, mul_one_div_cancel h2.ne',
      Real.rpow_one, Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)] at h4
    exact h4

end PositivityTheory.HtPt.Farsharp
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.Farsharp

section

@[expose] public section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
  (hp : v (p : C) < 1)


include hv hp in
theorem smul_dUnit_mem (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (hfin : {u : A | IsGroupLikeElem O u}.Finite) (q : O) (hq : q ≠ 0)
    (M : Submodule O (Cot O A)) (hM : ∀ u, IsGroupLikeElem O u → dUnit (R := O) u ∈ M)
    (hqM : ∀ y, q • y ∈ M) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (y : Cot O A) : κ • y ∈ M := by
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  let ε := counitAlgHom O A
  let π : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap
  have hπ : ∀ a, π a = a - algebraMap O A (ε a) := fun _ => rfl
  let μ : A ⊗[O] A →ₗ[O] A := LinearMap.mul' O A ∘ₗ TensorProduct.map π π
  have hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b := fun a b => by simp [μ]
  let N : Submodule O A := Submodule.span O {u : A | IsGroupLikeElem O u} ⊔
    (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))
  have hN : N.FG := (Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))
  have hNM : N ≤ M.comap (AugCot.d ε) := by
    refine sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      induction t with
      | tmul a b =>
        have h0 : ∀ a, ε (π a) = 0 := fun a => by rw [hπ]; simp
        rw [Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]
        exact zero_mem _
      | add x y hx hy =>
        change AugCot.d ε (μ (x + y)) ∈ M
        rw [map_add, map_add]
        exact add_mem hx hy
    · rintro _ ⟨a, rfl⟩
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      exact hqM _
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ y
  rw [← map_smul]
  refine hNM (mem_of_forall_dvd N hN hq
    (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)
  have hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u := fun u hu =>
    hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))
  rw [map_smul]
  refine dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a
  have h1 := hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))
  have h2 := (hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)
  have h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    rw [hμ, hπ, hπ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h3, map_add (f := _), map_sub, map_sub, map_smul, map_smul, map_smul] at h1
  exact (dvd_add_left h2).1 h1


include hv hp in
theorem smul_mem_range_dlogLinear [Algebra ℤ_[p] O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) :
    κ • w ∈ LinearMap.range (dlogLinear G) := by
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.2 hpp.ne_zero h1
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)),
      κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n) := fun κ hκ n y => by
    have hch : ∀ u (hu : IsGroupLikeElem O u),
        charFun O (G.A n) (toConv (evalPoint u hu)) = u := fun u hu =>
      CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ
    have : Finite (CartierDual O (G.A n) →ₐ[O] O) :=
      Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))
    refine smul_dUnit_mem p C v O hv hp (G.A n)
      ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O =>
        charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩)
      ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_)
      (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y
    obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
    refine ⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩
    rw [lev_apply, dlog_val, ← hch u hu, ← hχ]
    rfl
  refine smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w
  rw [map_natCast]
  exact pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'

theorem hodgeTateCokerSharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w
  obtain ⟨z, hz⟩ := smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w
  rw [← hz]
  clear hz
  induction z with
  | tmul c χ =>
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective χ
    exact ⟨c ⊗ₜ t, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

end PositivityTheory.HtPt.Farsharp
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateCokernelSharp

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_cokernel_sharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp :=
  PositivityTheory.HtPt.Farsharp.hodgeTateCokerSharp

end GlobalTheory.CompanionTheory.Ar.HT
end
end
