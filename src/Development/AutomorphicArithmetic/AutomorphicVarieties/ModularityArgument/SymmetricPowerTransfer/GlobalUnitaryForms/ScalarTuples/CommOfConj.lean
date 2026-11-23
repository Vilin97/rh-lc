module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SymbolEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import GroundTheory.GlobalFields.Adele.Approximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKGlob

section

@[expose] public section

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open NumberField IsDedekindDomain Matrix Loc

theorem lmap_re {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).re = f x.re := rfl

theorem lmap_im {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).im = f x.im := rfl

variable {F : Type} [Field F] [NumberField F]

theorem int_iff (v : Pl F) (x : Kv v) : IsIntegral (Ov v) x ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem int_glob (x : F) : IsIntegral ℤ x ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v x) := by
  simp only [int_iff]
  refine ⟨fun h v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨x, h⟩, fun h => ?_⟩
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v =>
    (GroundTheory.Global.coe_mem_adicCompletionIntegers_iff v x).1 (h v)
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

theorem den_glob (x : F) : ∃ c : ℕ, c ≠ 0 ∧ IsIntegral ℤ ((c : F) * x) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem approx_F (a : ∀ v : Pl F, Kv v) {e f : F} (he : e ≠ 0) (hf : f ≠ 0) (ha : ∀ v, IsIntegral (Ov v) (cv v e * a v)) :
    ∃ x : F, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = cv v x + cv v f * r := by
  let b : FiniteAdeleRing (𝓞 F) F := ⟨fun v => cv v e * a v, Filter.Eventually.of_forall fun v => (int_iff v _).1 (ha v)⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e * f)⁻¹ * b)
  refine ⟨f * k, fun v => ⟨cv v (e * f)⁻¹ * (cv v e * a v) - cv v k, (int_iff v _).2 (hk v), ?_⟩⟩
  have h1 : cv v e ≠ 0 := (map_ne_zero _).2 he
  have h2 : cv v f ≠ 0 := (map_ne_zero _).2 hf
  rw [map_inv₀, map_mul, map_mul]
  field_simp
  ring

theorem den_loc (v : Pl F) (x : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * x) := by
  have hU : IsOpen {w : Kv v | x - w ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (Kv v)).preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_mem_open hU ⟨x, by simp⟩
  obtain ⟨n, hn, h⟩ := den_glob z
  refine ⟨n, hn, ?_⟩
  have h1 := (int_glob _).1 h v
  rw [map_mul, map_natCast] at h1
  have e : (n : Kv v) * x = n * cv v z + n * (x - cv v z) := by ring
  rw [e]
  exact h1.add ((isIntegral_natCast (R := Ov v) (B := Kv v) n).mul ((int_iff v _).2 hz))

variable {Δ : F}

theorem int_cD {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) (v : Pl F) : IsIntegral (Ov v) ((c : Kv v) * cv v Δ) := by
  have h1 := (int_glob _).1 hc v
  rwa [map_mul, map_natCast] at h1

theorem approx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : Lsq F Δ, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = lmap (cv v) Δ x + n • r := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : F) ≠ 0 := Nat.cast_ne_zero.2 hc0
  obtain ⟨x, hx⟩ := approx_F (fun v => (a v).re) (e := 2) two_ne_zero hn' fun v => by
    rw [map_ofNat]; exact int_re _ (ha v)
  obtain ⟨y, hy⟩ := approx_F (fun v => (a v).im) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (mul_ne_zero hn' hc') fun v => by
    rw [map_mul, map_mul, map_ofNat, map_natCast]; exact int_im _ (int_cD hc v) (ha v)
  refine ⟨⟨x, y⟩, fun v => ?_⟩
  obtain ⟨r, hr, e1⟩ := hx v
  obtain ⟨s, hs, e2⟩ := hy v
  refine ⟨_, int_mk _ (int_cD hc v) hr hs, ?_⟩
  ext : 1
  · rw [e1]; simp [lmap]
  · rw [e2]; simp [lmap, mul_assoc]

variable (Δ)

abbrev MM : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

def RR : Subring (MM Δ) := ⨅ v, (RL (cv v Δ) (Ov v)).comap (Pi.evalRingHom _ v)

def jj : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* MM Δ := Pi.ringHom fun v => (lmap (cv v) Δ).mapMatrix

variable {Δ}

theorem mem_RR {m : MM Δ} : m ∈ RR Δ ↔ ∀ v, m v ∈ RL (cv v Δ) (Ov v) := Subring.mem_iInf

theorem jj_apply (y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) (v : Pl F) : jj Δ y v = y.map (lmap (cv v) Δ) := rfl

theorem pl_ne : Nonempty (Pl F) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩⟩

theorem lam_shape {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) : Shape y := by
  obtain ⟨v⟩ := pl_ne (F := F)
  exact shape_of_map (cv v) (mem_RR.1 h v).1

theorem lam_int {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) (i j : Fin 2) :
    IsIntegral ℤ (2 * (y i j).re) ∧ IsIntegral ℤ (2 * c * Δ * (y i j).im) := by
  have h1 : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ (y i j)) := fun v => by
    have h2 := (mem_RR.1 (Subring.mem_comap.1 h) v).2 i j
    rwa [jj_apply, Matrix.map_apply] at h2
  refine ⟨(int_glob _).2 fun v => ?_, (int_glob _).2 fun v => ?_⟩
  · have h2 := int_re _ (h1 v)
    rw [lmap_re] at h2
    rwa [map_mul, map_ofNat]
  · have h2 := int_im _ (int_cD hc v) (h1 v)
    rw [lmap_im] at h2
    rwa [map_mul, map_mul, map_mul, map_ofNat, map_natCast]

theorem lam_fg (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RR Δ).comap (jj Δ)) := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  let ψ : (RR Δ).comap (jj Δ) →+ (Fin 2 → Fin 2 → 𝓞 F × 𝓞 F) := AddMonoidHom.mk'
    (fun y i j => (⟨_, (lam_int hc y.2 i j).1⟩, ⟨_, (lam_int hc y.2 i j).2⟩)) fun x y => by
      funext i j
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact mul_add _ _ _
      · exact mul_add _ _ _
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Matrix.ext fun i j => ?_)
  have h1 := congrFun (congrFun h i) j
  exact QuadraticAlgebra.ext (mul_left_cancel₀ two_ne_zero (congrArg Subtype.val (congrArg Prod.fst h1)))
    (mul_left_cancel₀ (by simp [hc0, hΔ]) (congrArg Subtype.val (congrArg Prod.snd h1)))

theorem approx_R (hΔ : Δ ≠ 0) : ∀ m ∈ RR Δ, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ (RR Δ).comap (jj Δ), ∃ r ∈ RR Δ, m = jj Δ x + (n : MM Δ) * r := by
  intro m hm n hn
  obtain ⟨a, ha⟩ := approx_L hΔ (fun v => m v 0 0) (fun v => (mem_RR.1 hm v).2 0 0) hn
  obtain ⟨b, hb⟩ := approx_L hΔ (fun v => m v 0 1) (fun v => (mem_RR.1 hm v).2 0 1) hn
  choose r hr ha using ha
  choose s hs hb using hb
  have h1 : (fun v => qm (r v) (s v) : MM Δ) ∈ RR Δ := mem_RR.2 fun v => qm_mem _ (hr v) (hs v)
  have e : m = jj Δ (qm a b) + (n : MM Δ) * fun v => qm (r v) (s v) := by
    funext v
    rw [← nsmul_eq_mul, Pi.add_apply, Pi.smul_apply, jj_apply, qm_map, (mem_RR.1 hm v).1.eq, ha v, hb v]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [qm, add_comm]
  refine ⟨qm a b, ?_, _, h1, e⟩
  rw [Subring.mem_comap, ← sub_eq_of_eq_add e]
  exact sub_mem hm (mul_mem (natCast_mem _ n) h1)

theorem form_pos (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (σ : F →+* ℝ) (a b : Lsq F Δ) :
    let d := σ (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2)
    σ a.re ^ 2 ≤ d ∧ σ b.re ^ 2 ≤ d ∧ -σ Δ * σ a.im ^ 2 ≤ d ∧ -σ Δ * σ b.im ^ 2 ≤ d := by
  have h := hneg σ
  have h1 : 0 ≤ -σ Δ * σ a.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -σ Δ * σ b.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  simp only [map_add (f := _), map_sub, map_mul, map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (σ a.re), sq_nonneg (σ b.re)]

theorem real_emb [IsTotallyReal F] (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, (σ x : ℂ) = φ x :=
  ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, fun x => ComplexEmbedding.IsReal.coe_embedding_apply _ x⟩

theorem unit_of_shape [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : Shape y) (h0 : y ≠ 0) :
    ∃ g : DX Δ, mt g = y := by
  rw [h.eq]
  refine exists_DX fun hd => h0 ?_
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := real_emb φ
  have := form_pos hneg σ (y 0 0) (y 0 1)
  rw [hd, map_zero] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  have hσ := hneg σ
  have z : ∀ x : F, σ x ^ 2 ≤ 0 → x = 0 := fun x hx => (map_eq_zero σ).1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hx (sq_nonneg _)))
  have a0 : y 0 0 = 0 := QuadraticAlgebra.ext (z _ h1) (z _ (by nlinarith [sq_nonneg (σ (y 0 0).im)]))
  have b0 : y 0 1 = 0 := QuadraticAlgebra.ext (z _ h2) (z _ (by nlinarith [sq_nonneg (σ (y 0 1).im)]))
  rw [h.eq, a0, b0]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm]

theorem box_fin [IsTotallyReal F] {e : F} (he : e ≠ 0) (d : F) :
    {x : F | IsIntegral ℤ (e * x) ∧ ∀ σ : F →+* ℝ, σ (e * x) ^ 2 ≤ σ d}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, (‖φ d‖ + 1))
  refine (h.preimage (f := fun x : F => e * x) (mul_right_injective₀ he).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ d‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ φ))
  obtain ⟨σ, hσ⟩ := real_emb φ
  have h1 := hA σ
  rw [← hσ, ← hσ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [← sq_abs] at h1
  nlinarith [le_abs_self (σ d), abs_nonneg (σ (e * x)), sq_nonneg (|σ (e * x)| - 1), abs_nonneg (σ d)]

theorem det_fin [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (hΔ : Δ ≠ 0) (d : Lsq F Δ) :
    {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ) | y ∈ (RR Δ).comap (jj Δ) ∧ y.det = d}.Finite := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have h1 := box_fin (F := F) (e := 2) two_ne_zero (4 * d.re)
  have h2 := box_fin (F := F) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (-(4 * c ^ 2 * Δ) * d.re)
  refine ((((h1.prod h2).prod (h1.prod h2)).image fun p => qm ⟨p.1.1, p.1.2⟩ ⟨p.2.1, p.2.2⟩)).subset ?_
  rintro y ⟨hy, hd⟩
  have hs := lam_shape hy
  refine ⟨(((y 0 0).re, (y 0 0).im), ((y 0 1).re, (y 0 1).im)), ?_, hs.eq.symm⟩
  rw [hs.eq, det_qm] at hd
  have hd' : d.re = (y 0 0).re ^ 2 - Δ * (y 0 0).im ^ 2 + (y 0 1).re ^ 2 - Δ * (y 0 1).im ^ 2 := by rw [← hd]; rfl
  have k1 : ∀ (σ : F →+* ℝ) (x : F), σ x ^ 2 ≤ σ d.re → σ (2 * x) ^ 2 ≤ σ (4 * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat]; nlinarith
  have k2 : ∀ (σ : F →+* ℝ) (x : F), -σ Δ * σ x ^ 2 ≤ σ d.re → σ (2 * c * Δ * x) ^ 2 ≤ σ (-(4 * c ^ 2 * Δ) * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat, map_neg, map_pow, map_natCast]
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * (c : ℝ) ^ 2 * -σ Δ from mul_nonneg (by positivity) (by linarith [hneg σ]))
    nlinarith
  have f := fun σ => form_pos hneg σ (y 0 0) (y 0 1)
  rw [← hd'] at f
  exact ⟨⟨⟨(lam_int hc hy 0 0).1, fun σ => k1 σ _ (f σ).1⟩, (lam_int hc hy 0 0).2, fun σ => k2 σ _ (f σ).2.2.1⟩,
    ⟨(lam_int hc hy 0 1).1, fun σ => k1 σ _ (f σ).2.1⟩, (lam_int hc hy 0 1).2, fun σ => k2 σ _ (f σ).2.2.2⟩


variable (Δ) in
def rho : DA Δ →* MM Δ where
  toFun g v := mt (g.1 v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem den_rho (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ (n : MM Δ) * rho Δ g ∈ RR Δ := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hT : {v : Pl F | g.1 v ∉ KD (cv v Δ) (Ov v)}.Finite := Filter.eventually_cofinite.1 g.2
  choose n hn0 hn using fun v : Pl F => den_mat (Ov v) (c := c)
    (by rw [← map_natCast (cv v)]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hc0)) (int_cD hc v) (den_loc v) (shape_mt (g.1 v))
  refine ⟨∏ v ∈ hT.toFinset, n v, Finset.prod_ne_zero_iff.2 fun v _ => hn0 v, mem_RR.2 fun v => ?_⟩
  rw [← nsmul_eq_mul, Pi.smul_apply]
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact nsmul_mem ((mem_KD _ _).1 hv).1 _
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hT.mem_toFinset.2 hv)
    rw [hk, mul_nsmul, nsmul_eq_mul (n v)]
    exact nsmul_mem (hn v) k

end UpperTheory.V.Z.Sym.Glob.FK
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj

section

@[expose] public section

open Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Glob.FK

private theorem relIndex_ne {Γ X : Type} [Group Γ] (C H : Subgroup Γ) (φ : Γ → X) (s : Set X) (hs : s.Finite)
    (hmem : ∀ γ ∈ H, φ γ ∈ s) (hinj : ∀ γ δ, φ γ = φ δ → γ⁻¹ * δ ∈ C) : C.relIndex H ≠ 0 := by
  classical
  haveI : Finite s := hs.to_subtype
  let F : s → H ⧸ C.subgroupOf H := fun x =>
    if h : ∃ a : H, φ a = (x : X) then QuotientGroup.mk h.choose else QuotientGroup.mk 1
  haveI : Finite (H ⧸ C.subgroupOf H) := by
    refine Finite.of_surjective F ?_
    intro q
    refine QuotientGroup.induction_on q fun a => ?_
    have hex : ∃ b : H, φ b = ((⟨φ a, hmem a a.2⟩ : s) : X) := ⟨a, rfl⟩
    refine ⟨⟨φ a, hmem a a.2⟩, ?_⟩
    simp only [F, dif_pos hex]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hinj _ _ hex.choose_spec
  exact Subgroup.index_ne_zero_of_finite

private theorem conj_abs {A M Γ G : Type} [Ring A] [Ring M] [Group Γ] [Group G] (j : A →+* M) (R : Subring M) (ι : Γ →* G) (σ : Γ →* A)
    (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (σ γ)) (U : Subgroup G) (hU : ∀ u ∈ U, ∀ r ∈ R, ρ u * r * ρ u⁻¹ ∈ R)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) (g : G) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ b ∈ R.comap j, ∀ γ ∈ (U.map (MulAut.conj g).toMonoidHom).comap ι, N • (σ γ * b * σ γ⁻¹) ∈ R.comap j := by
  obtain ⟨n1, hn1, h1⟩ := hden g
  obtain ⟨n2, hn2, h2⟩ := hden g⁻¹
  refine ⟨n1 * n2 * (n1 * n2), mul_ne_zero (mul_ne_zero hn1 hn2) (mul_ne_zero hn1 hn2), ?_⟩
  intro b hb γ hγ
  rw [Subgroup.mem_comap, Subgroup.mem_map] at hγ
  obtain ⟨u, hu, hug⟩ := hγ
  have hιγ : ι γ = g * u * g⁻¹ := by
    rw [← hug]
    simp [MulAut.conj_apply]
  have hιγ' : ι γ⁻¹ = g * u⁻¹ * g⁻¹ := by
    rw [map_inv, hιγ]
    group
  rw [Subring.mem_comap] at hb ⊢
  rw [nsmul_eq_mul, map_mul, map_mul, map_mul, map_natCast, ← hι, ← hι, hιγ, hιγ', map_mul, map_mul, map_mul, map_mul]
  have key : ((n1 * n2 * (n1 * n2) : ℕ) : M) * (ρ g * ρ u * ρ g⁻¹ * j b * (ρ g * ρ u⁻¹ * ρ g⁻¹)) =
      ((n1 : M) * ρ g) * (ρ u * (((n2 : M) * ρ g⁻¹) * j b * ((n1 : M) * ρ g)) * ρ u⁻¹) * ((n2 : M) * ρ g⁻¹) := by
    simp only [← nsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    ring
  rw [key]
  exact R.mul_mem (R.mul_mem h1 (hU u hu _ (R.mul_mem (R.mul_mem h2 hb) h1))) h2

private theorem comm_of_conj {A Γ : Type} [Ring A] [Group Γ] (σ : Γ →* A) (b : A) (γ δ : Γ) (h : σ γ * b * σ γ⁻¹ = σ δ * b * σ δ⁻¹) :
    σ (γ⁻¹ * δ) * b = b * σ (γ⁻¹ * δ) := by
  have e1 : σ γ⁻¹ * σ γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : σ δ⁻¹ * σ δ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul]
  calc σ γ⁻¹ * σ δ * b = σ γ⁻¹ * (σ δ * b * σ δ⁻¹) * σ δ := by simp only [mul_assoc, e2, mul_one]
    _ = σ γ⁻¹ * (σ γ * b * σ γ⁻¹) * σ δ := by rw [h]
    _ = b * (σ γ⁻¹ * σ δ) := by simp only [← mul_assoc, e1, one_mul]

private noncomputable def sg {K : Type} [Field K] (Δ : K) : DX Δ →* Matrix (Fin 2) (Fin 2) (Lsq K Δ) where
  toFun := mt
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem stab_F {F G : Type} [Field F] [CharZero F] [Group G] {Δ : F} (hΔ : Δ ≠ 0) {M : Type} [Ring M]
    (j : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* M) (R : Subring M) (ι : DX Δ →* G)
    (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (sg Δ γ)) (U : Subgroup G) (hU : ∀ u ∈ U, ∀ r ∈ R, ρ u * r * ρ u⁻¹ ∈ R)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) (hfin : ∀ d, {y | y ∈ R.comap j ∧ y.det = d}.Finite)
    {c : F} (hc : c ≠ 0) (h1 : qm ⟨0, c⟩ 0 ∈ R.comap j) (h2 : qm 0 1 ∈ R.comap j) (g : G) :
    (ZD Δ).relIndex ((U.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  classical
  obtain ⟨N, hN, hNmem⟩ := conj_abs j R ι (sg Δ) ρ hι U hU hden g
  have hcan : ∀ x y : Matrix (Fin 2) (Fin 2) (Lsq F Δ), N • x = N • y → x = y := by
    intro x y h
    have h' : (N : F) • x = (N : F) • y := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      exact h
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN) h'
  have hdet : ∀ (γ : DX Δ) (b : Matrix (Fin 2) (Fin 2) (Lsq F Δ)),
      (N • (sg Δ γ * b * sg Δ γ⁻¹)).det = (N • b).det := by
    intro γ b
    have e : N • (sg Δ γ * b * sg Δ γ⁻¹) = sg Δ γ * (N • b) * sg Δ γ⁻¹ := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (sg Δ γ)), mul_assoc, ← Matrix.det_mul,
      ← map_mul, mul_inv_cancel, map_one, Matrix.det_one, mul_one]
  refine relIndex_ne (ZD Δ) ((U.map (MulAut.conj g).toMonoidHom).comap ι)
    (fun γ => (N • (sg Δ γ * qm ⟨0, c⟩ 0 * sg Δ γ⁻¹), N • (sg Δ γ * qm 0 1 * sg Δ γ⁻¹)))
    ({y | y ∈ R.comap j ∧ y.det = (N • qm (⟨0, c⟩ : Lsq F Δ) 0).det} ×ˢ
      {y | y ∈ R.comap j ∧ y.det = (N • qm (0 : Lsq F Δ) 1).det})
    ((hfin _).prod (hfin _)) ?_ ?_
  · intro γ hγ
    exact ⟨⟨hNmem _ h1 γ hγ, hdet γ _⟩, ⟨hNmem _ h2 γ hγ, hdet γ _⟩⟩
  · intro γ δ h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h
    have c1 := comm_of_conj (sg Δ) _ γ δ (hcan _ _ e1)
    have c2 := comm_of_conj (sg Δ) _ γ δ (hcan _ _ e2)
    exact FK.mem_ZD hΔ hc (γ⁻¹ * δ) c1 c2

private theorem mem_box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := Subgroup.mem_iInf

private theorem finK_fin (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ) (hD : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    (∃ S : Finset (DA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ D.UZ, g = ι γ * s * u) ∧
    ∀ g, (ZD Δ).relIndex ((D.UZ.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  classical
  haveI := hD.real
  have hΔ : Δ ≠ 0 := by
    intro h0
    obtain ⟨σ, -⟩ := FK.real_emb (Classical.arbitrary (F →+* ℂ))
    have h := hD.neg σ
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hιρ : ∀ γ, rho Δ (ι γ) = jj Δ (sg Δ γ) := by
    intro γ
    funext v
    rw [FK.jj_apply]
    exact hι γ v
  have hU : ∀ u ∈ D.UZ, ∀ r ∈ RR Δ, rho Δ u * r * rho Δ u⁻¹ ∈ RR Δ := by
    intro u hu r hr
    rw [FK.mem_RR] at hr ⊢
    intro v
    have huv := (mem_box _ _ u).1 hu v
    have hle : ZD ((cv v) Δ) ⊔ D.J2v v ≤ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
      refine sup_le_sup_left ?_ _
      unfold Dat.J2v
      split_ifs with hv
      · exact (hD.sig v hv).levelTwoLeIntegral
      · exact le_rfl
    exact FK.conj_mem (Ov v) (hle huv) (hr v)
  have hfin := FK.det_fin hD.neg hΔ
  obtain ⟨c, hc0, hcint⟩ := FK.den_glob Δ
  have hq1 : qm (⟨0, (c : F)⟩ : Lsq F Δ) 0 ∈ (RR Δ).comap (jj Δ) := by
    rw [Subring.mem_comap, FK.mem_RR]
    intro v
    rw [FK.jj_apply, FK.qm_map]
    have e : (lmap (cv v) Δ) (⟨0, (c : F)⟩ : Lsq F Δ) = ⟨0, (c : Kv v)⟩ := by
      simp [lmap]
    rw [e, map_zero]
    exact FK.qm_mem (Ov v) (FK.int_om (Ov v) (FK.int_cD hcint v)) isIntegral_zero
  have hq2 : qm (0 : Lsq F Δ) 1 ∈ (RR Δ).comap (jj Δ) := by
    rw [Subring.mem_comap, FK.mem_RR]
    intro v
    rw [FK.jj_apply, FK.qm_map, map_zero, map_one]
    exact FK.qm_mem (Ov v) isIntegral_zero isIntegral_one
  refine ⟨?_, fun g => stab_F hΔ (jj Δ) (RR Δ) ι (rho Δ) hιρ D.UZ hU FK.den_rho hfin
    (Nat.cast_ne_zero.2 hc0) hq1 hq2 g⟩
  haveI := FK.lam_fg hΔ
  haveI : CharZero (Matrix (Fin 2) (Fin 2) (Lsq F Δ)) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  have hbig := cls_abs (jj Δ) (RR Δ) ι (sg Δ) (rho Δ) hιρ
    ((rpg (fun v => DX ((cv v) Δ)) fun v => KD ((cv v) Δ) (Ov v)).box fun v => KD ((cv v) Δ) (Ov v))
    (by
      intro g h1 h2
      rw [mem_box]
      intro v
      rw [FK.mem_KD]
      rw [FK.mem_RR] at h1 h2
      exact ⟨h1 v, h2 v⟩)
    (by
      intro y hy hy0
      obtain ⟨γ, hγ⟩ := FK.unit_of_shape hD.neg (FK.lam_shape hy) hy0
      exact ⟨γ, hγ⟩)
    (FK.approx_R hΔ) FK.den_rho
  refine cls_of_relIndex ι _ D.UZ ?_ hbig
  refine box_relIndex _ _ _ D.Sg (fun v hv => ?_) (fun v hv => ?_)
  · unfold Dat.J2v
    rw [if_pos hv]
    exact ne_zero_of_dvd_ne_zero (hD.sig v hv).levelTwoFiniteIndex (Subgroup.relIndex_dvd_of_le_left _ le_sup_right)
  · unfold Dat.J2v
    rw [if_neg hv]
    exact le_sup_right

theorem UpperTheory.V.Z.Sym.Glob.finK :
    UpperTheory.V.Z.Sym.Glob.FinK := by
  intro F _ _ Δ D hD V _ _ ch B hB
  refine ⟨?_, finK_test F Δ D hD V ch B hB⟩
  obtain ⟨hcls, hstab⟩ := finK_fin F Δ D hD B.ι hB.ι
  refine ⟨?_, ?_⟩
  · rw [hB.U]
    exact hcls
  · intro g
    rw [hB.U, hB.Γ₀]
    exact hstab g
end
end
