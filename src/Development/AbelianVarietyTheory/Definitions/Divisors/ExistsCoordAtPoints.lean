module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMapStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K), y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | exact GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | (intros; apply GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmulStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightScaling.pointHeight_smul | exact GlobalTheory.Adelic.HeightScaling.pointHeight_smul | (intros; apply GlobalTheory.Adelic.HeightScaling.pointHeight_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecHeightSmulAlgebraMap

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic

theorem vecHeight_smul_algebraMap (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hw : Submodule.span F (Set.range w.col) = ⊤) (hA : ∀ σ, (A σ).det ≠ 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    (y : Fin N → K) (c : Ω) (hy : y ≠ 0) (hc : c ≠ 0) :
    vecHeight w A (c • fun j => algebraMap K Ω (y j)) = pointHeight w A y := by
  set z : Fin N → Ω := c • fun j => algebraMap K Ω (y j) with hz
  let L : IntermediateField K Ω := IntermediateField.adjoin K {c}
  have hcK : IsIntegral K c := ((Algebra.IsAlgebraic.isAlgebraic (R := F) c).tower_top K).isIntegral
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hcK
  haveI : NumberField L := NumberField.of_module_finite K L
  have hcL : c ∈ L := IntermediateField.mem_adjoin_simple_self K c
  have hle : coordField F z ≤ L.restrictScalars F := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨j, rfl⟩
    exact mul_mem hcL (L.algebraMap_mem (y j))
  let ι : coordField F z →ₐ[F] L := IntermediateField.inclusion hle
  letI : Algebra (coordField F z) L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (coordField F z) L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let z' : Fin N → coordField F z := fun j => ⟨z j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  let c' : L := ⟨c, hcL⟩
  have hc' : c' ≠ 0 := fun h => hc (congrArg Subtype.val h)
  have hyL : (fun j => algebraMap K L (y j)) ≠ 0 := fun h => hy (funext fun j =>
    (algebraMap K L).injective ((congrFun h j).trans (map_zero _).symm))
  have he : (fun j => algebraMap (coordField F z) L (z' j)) = c' • fun j => algebraMap K L (y j) :=
    funext fun j => Subtype.ext rfl
  have hz' : z' ≠ 0 := fun h => smul_ne_zero hc' hyL (by
    rw [← he, h]; exact funext fun j => map_zero _)
  have h1 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F (coordField F z) N n w A hw hA L z' hz'
  have h2 := GlobalTheory.T.normalizedPointHeightLattice_smul F L N n w A hw hA _ c' hyL hc'
  have h3 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F K N n w A hw hA L y hy
  rw [he, h2, h3] at h1
  exact h1.symm

end GlobalTheory.Adelic
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

abbrev RatPt (G : Geo K) (s : Fin G.D → Fin G.N → K) : Type := PtsOver K ((G.ideal s).subschemeι ≫ G.str)

namespace RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K} (x : RatPt G s)

def pt : G.Pt K := ⟨x.1 ≫ (G.ideal s).subschemeι, (Category.assoc _ _ _).trans x.2⟩

def along {Ω : Type} [Field Ω] (φ : K →+* Ω) : Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ) :=
  ⟨spMap φ ≫ x.1, by rw [Category.assoc, x.2, spMap, spMap, ← Spec.map_comp]; rfl⟩

def gen (k : Fin G.n) : K := ∑ j, G.w j k * G.coords x.pt.1 j

def c₁ (τ : K →+* ℂ) : ℝ := archSize (G.A τ) fun j => τ (G.coords x.pt.1 j)

def c₂ (τ : K →+* ℂ) : ℝ := archSize (G.A₂ τ) fun j => τ (G.second.coords x.pt.1 j)

def ht : ℝ := vecHt x.gen x.c₁

theorem le_chart (j : ℤ) : ⊤ ≤ (x.1 ≫ (G.ideal s).subschemeι) ⁻¹ᵁ (tw G.L₂ G.L j).U
    (twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
  fun _ hw => mem_tw_U.2 ⟨G.second.le_chartAt x.pt.1 hw, G.le_chartAt x.pt.1 hw⟩

def val (j : ℕ) : G.SecOn s j →ₗ[K] K where
  toFun g := valOn x.1 _ (x.le_chart j) g
  map_add' f g := map_add _ f g
  map_smul' c g := valOn_smul x.1 x.2 _ _ c g

theorem c₁_pos (τ : K →+* ℂ) : 0 < x.c₁ τ := archSize_pos (G.herm τ) fun h =>
  G.geom.alg.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem c₂_pos (τ : K →+* ℂ) : 0 < x.c₂ τ := archSize_pos (G.herm₂ τ) fun h =>
  G.alg₂.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem c₂_conj (τ : K →+* ℂ) : x.c₂ ((starRingEnd ℂ).comp τ) = x.c₂ τ := by
  let w (σ : K →+* ℂ) : CxPts G.str σ := Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap σ) (x.along σ)
  have e (σ : K →+* ℂ) : (G.φ₂ σ).φ (G.second.chartAt (ptOf x.pt.1)) (w σ) = Real.log (x.c₂ σ ^ 2) := by
    refine (G.second.weight_φ _ _ σ _ (w σ)).trans (congrArg (fun y => Real.log (archSize _ y ^ 2)) (funext fun k => ?_))
    exact Points.valR_spMap_comp σ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
  have h := G.isConj_φ₂ τ (G.second.chartAt (ptOf x.pt.1)) (w τ) (w _) (by
    change (spMap _ ≫ x.1) ≫ _ = spMap _ ≫ (spMap τ ≫ x.1) ≫ _
    rw [← Category.assoc (spMap (starRingEnd ℂ)), ← Category.assoc (spMap (starRingEnd ℂ)), ← Spec.map_comp]
    rfl) fun _ _ => G.second.le_chartAt x.pt.1 (Set.mem_univ _)
  have p := x.c₂_pos τ
  have p' := x.c₂_pos ((starRingEnd ℂ).comp τ)
  exact (pow_left_inj₀ p'.le p.le two_ne_zero).1
    (Real.log_injOn_pos (pow_pos p' 2) (pow_pos p 2) ((e _).symm.trans (h.trans (e τ))))

theorem exp_neg_weight (j : ℕ) (τ : K →+* ℂ) :
    Real.exp (-(Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ)) = ((x.c₂ τ * x.c₁ τ ^ j) ^ 2)⁻¹ := by
  have e : (Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ) = Real.log (x.c₂ τ ^ 2) + j * Real.log (x.c₁ τ ^ 2) := by
    simp only [Geo.weightOn, Weight.pull, Weight.linComb, Geo.φTw, Weight.tens, Weight.zpow, Geo.φ, Geo.φ₂,
      HermSys.weight_φ]
    have a₁ : ∀ k, secVal G.str τ (G.b k) (G.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.le_chartAt x.pt.1) _
    have a₂ : ∀ k, secVal G.str τ (G.b₂ k) (G.second.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.second.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
    simp only [id, a₁, a₂, Finset.univ_unique, Finset.sum_singleton, Int.cast_one, one_mul, Int.cast_natCast, c₁, c₂]
  have p₁ := x.c₁_pos τ
  have p₂ := x.c₂_pos τ
  rw [e, Real.exp_neg, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity), mul_pow,
    ← pow_mul, ← pow_mul, mul_comm 2 j]

theorem nsq_eq (j : ℕ) (τ : K →+* ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) (g : ι → G.SecOn s j) :
    (Geo.weightOn s j τ).nsq (∑ i, c i • cval τ (g i)) (x.along τ) =
      ‖∑ i, c i * τ (x.val j (g i))‖ ^ 2 / (x.c₂ τ * x.c₁ τ ^ j) ^ 2 := by
  have hw : x.along τ ∈ ptsIn ((G.ideal s).subschemeι ≫ G.str) τ (((tw G.L₂ G.L j).pull (G.ideal s).subschemeι).U
      fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
    fun _ _ => mem_pull.2 (x.le_chart j (Set.mem_univ _))
  rw [Weight.nsq_eq _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (cval_mem τ (g i))) hw, exp_neg_weight,
    div_eq_mul_inv]
  refine congrArg (fun r => ‖r‖ ^ 2 * _) ?_
  refine ((congrFun (Finset.sum_apply _ _ _) _).trans (Finset.sum_apply _ _ _)).trans ?_
  exact Finset.sum_congr rfl fun i _ => congrArg (c i * ·)
    ((cval_eq_val τ _ _ _ mem_ptsIn_top hw).trans (evalPt_spMap_comp τ x.1 _ _ _ _))

theorem val_mulSecOn (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j) :
    x.val (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) =
      (∑ k, u k * G.coords x.pt.1 k) * x.val j g := by
  refine (valOn_mulSecOn G.isLB₂ G.isLB (G.comb u) _ g x.1 _ _ (G.le_chartAt x.pt.1) (x.le_chart j)
    (x.le_chart _)).trans (congrArg (· * _) ?_)
  refine (Points.valR_eq _ _ (G.le_chartAt x.pt.1) _).symm.trans ((G.val_comb x.pt.1 u).trans ?_)
  rw [LinSys.baseHom_ptOver]
  rfl

theorem along_injective (hs : G.IsGood s) {Ω : Type} [Field Ω] (φ : K →+* Ω) :
    Function.Injective fun x : RatPt G s => x.along φ := fun x x' h => by
  have := hs.finite
  have : IsAffine (G.ideal s).subscheme := isAffine_of_isAffineHom ((G.ideal s).subschemeι ≫ G.str)
  have e : spMap φ ≫ x.1 = spMap φ ≫ x'.1 := congrArg Subtype.val h
  refine Subtype.ext (ext_evalPt (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => φ.injective ?_))
  rw [← evalPt_spMap_comp φ x.1 ⊤ le_top le_top, ← evalPt_spMap_comp φ x'.1 ⊤ le_top le_top]
  simp only [e]

end RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K}

def Coord.AtPoints {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (x : Fin δ ≃ RatPt G s) : Prop :=
  ∀ p, (∀ j g, Co.ev j g p = (x p).val j g) ∧ Co.y p = G.coords (x p).pt.1 ∧ ∀ τ, Co.c₂ τ p = (x p).c₂ τ

theorem RatPt.along_bijective (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (φ : K →+* Ω) : Function.Bijective fun x : RatPt G s => x.along φ := by
  have := hs.finite
  have := hs.etale
  letI := φ.toAlgebra
  have hB := isLB_tw G.isLB₂ G.isLB 0
  have : Finite (Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ)) := finite_ptsOver _ Ω
  refine (RatPt.along_injective hs φ).bijective_of_nat_card_le (le_of_eq ?_)
  exact (finrank_H0On (p := G.str) (I := G.ideal s) hB Ω).symm.trans
    ((finrank_H0On hB (AlgebraicClosure K)).trans (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, h⟩).symm)

theorem exists_coord_atPoints (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {δ : ℕ} (x : Fin δ ≃ RatPt G s) : ∃ Co : Coord G hs δ, Co.AtPoints x := by
  have := hs.finite
  have := hs.etale
  let φ (j : ℕ) : G.SecOn s j →ₗ[K] (Fin δ → K) := LinearMap.pi fun p => (x p).val j
  have bij (j : ℕ) : Function.Bijective (φ j) := by
    have hB := isLB_tw G.isLB₂ G.isLB (j : ℤ)
    choose r hr using h
    have inj : Function.Injective (φ j) := (injective_iff_map_eq_zero _).2 fun g hg => by
      have hr' (w : PtsOver (AlgebraicClosure K) ((G.ideal s).subschemeι ≫ G.str)) :
          w.1 = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 := (congrArg Subtype.val (hr w)).symm
      refine eq_zero_of_forall_valOn_eq_zero (Ω := AlgebraicClosure K) hB
        (fun w => twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1)))
        (fun w => by rw [hr' w]; exact fun _ _ => (r w).le_chart j (Set.mem_univ _)) fun w => ?_
      have e : (r w).val j g = 0 := by simpa [φ] using congrFun hg (x.symm (r w))
      have key : ∀ (z : Sp (AlgebraicClosure K) ⟶ (G.ideal s).subscheme) (hz),
          z = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 →
          valOn z (twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1))) hz g = 0 := by
        rintro _ hz rfl
        exact (evalPt_spMap_comp _ (r w).1 _ _ _ _).trans ((congrArg _ e).trans (map_zero _))
      exact key _ _ (hr' w)
    have := finite_H0On (p := G.str) (I := G.ideal s) hB
    refine ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 inj⟩
    rw [finrank_H0On hB (AlgebraicClosure K), Module.finrank_fin_fun, ← Nat.card_fin δ, Nat.card_congr x]
    exact (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, fun w => ⟨r w, hr w⟩⟩).symm
  refine ⟨⟨fun j => LinearEquiv.ofBijective (φ j) (bij j), fun p => G.coords (x p).pt.1, fun σ p => (x p).c₂ σ,
    fun _ => G.geom.alg.bpf.coords_ne_zero _, fun σ p => (x p).c₂_pos σ, fun σ p => (x p).c₂_conj σ,
    fun j u g => funext fun p => (x p).val_mulSecOn j u g, fun j σ m c g => ?_⟩, fun p => ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩⟩
  refine (csq_pointHerm _ _ _ σ c g).trans ?_
  rw [← finsum_comp_equiv (x.trans (Equiv.ofBijective _ (RatPt.along_bijective hs h σ))), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).nsq_eq j σ c g

section Split

variable {F : Type} [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]
  (s : Fin G.D → Fin G.N → E)

def RatPt.geomPt (x : RatPt (G.baseChange E) s) : (G.toLinSys.baseChange E).Pt (AlgebraicClosure E) :=
  Points.PtsOver.map ((G.baseChange E).ideal s).subschemeι rfl _ (x.along (algebraMap E (AlgebraicClosure E)))

variable {G E s}

theorem RatPt.ptHeight_geomPt (x : RatPt (G.baseChange E) s) :
    haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
    G.ptHeight (LinSys.toBase (RatPt.geomPt G E s x)) = x.ht := by
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
  obtain ⟨c, hc, e⟩ := G.exists_coords_baseChange E x.pt.1
  have h₀ := G.geom.alg.bpf.coords_ne_zero (x.pt.1 ≫ G.bcFst E)
  have h₁ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm (AlgebraicClosure E) _ 1 h₀ one_ne_zero
  have h₃ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ c h₀ hc
  have h₄ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ 1 (smul_ne_zero hc h₀) one_ne_zero
  rw [one_smul] at h₁ h₄
  have h₅ : G.coords (LinSys.toBase (RatPt.geomPt G E s x)).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords (x.pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  rw [HermSys.ptHeight, h₅, h₁]
  exact (h₃.symm.trans h₄).trans (congrArg (pointHeight G.w G.A) e.symm)

theorem Split.along_surjective (h : Split G.toTuple E s) :
    Function.Surjective fun x : RatPt (G.baseChange E) s => x.along (algebraMap E (AlgebraicClosure E)) := fun w => by
  obtain ⟨x₀, e⟩ := h w.1 w.2
  refine ⟨⟨x₀, ?_⟩, Subtype.ext e.symm⟩
  have h₁ := (G.baseChange E).comp_str (x₀ ≫ ((G.baseChange E).ideal s).subschemeι)
  have h₃ := (Category.assoc _ _ _).symm.trans h₁
  have h₂ := (Spec.map_comp _ _).trans ((congrArg (spMap (algebraMap E (AlgebraicClosure E)) ≫ ·) h₃).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).symm.trans w.2)))
  refine h₃.trans (congrArg spMap (RingHom.ext fun a => (algebraMap E (AlgebraicClosure E)).injective ?_))
  exact congrArg (fun f => f.hom a) (Spec.map_injective h₂)

theorem Split.geomPts_eq (h : Split G.toTuple E s) :
    G.geomPts E (G.linSection E s) = Set.range (RatPt.geomPt G E s) := by
  refine Set.ext fun y => ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨_, congrArg Subtype.val hx⟩⟩
  obtain ⟨x, hx⟩ := h.along_surjective ⟨z, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hz).trans y.2)⟩
  exact ⟨x, Subtype.ext ((congrArg (fun t => t.1 ≫ _) hx).trans hz)⟩

theorem RatPt.geomPt_injective (hs : (G.baseChange E).IsGood s) : Function.Injective (RatPt.geomPt G E s) :=
  fun _ _ h => RatPt.along_injective hs _ (Subtype.ext ((cancel_mono ((G.baseChange E).ideal s).subschemeι).1
    (congrArg Subtype.val h)))

theorem Split.exists_coord (h : Split G.toTuple E s) (hs : (G.baseChange E).IsGood s) :
    ∃ (x : Fin (G.geomPts E (G.linSection E s)).ncard ≃ RatPt (G.baseChange E) s)
      (Co : Coord (G.baseChange E) hs (G.geomPts E (G.linSection E s)).ncard),
      Co.AtPoints x ∧ G.cycleHeight E (G.linSection E s) = ∑ p, (x p).ht := by
  have hfin := (Geo.isGood_baseChange_iff.1 hs).finite_geomPts
  have : Finite (RatPt (G.baseChange E) s) :=
    (Set.finite_range_iff (RatPt.geomPt_injective hs)).1 (h.geomPts_eq ▸ hfin)
  have e : Nat.card (RatPt (G.baseChange E) s) = (G.geomPts E (G.linSection E s)).ncard := by
    rw [h.geomPts_eq, Set.ncard_range_of_injective (RatPt.geomPt_injective hs)]
  let x := (Finite.equivFinOfCardEq e).symm
  obtain ⟨Co, hCo⟩ := exists_coord_atPoints hs h.along_surjective x
  refine ⟨x, Co, hCo, ?_⟩
  rw [HermSys.cycleHeight]
  refine (finsum_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
  rw [finsum_mem_range (RatPt.geomPt_injective hs), ← finsum_comp_equiv x, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).ptHeight_geomPt

end Split

end GlobalTheory.HSCore
end
end
end
