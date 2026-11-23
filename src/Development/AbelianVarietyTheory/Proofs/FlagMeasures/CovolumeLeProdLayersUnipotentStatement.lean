module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPowStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeProductOverGradingLayersStatement
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShear

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem measurePreserving_layer_shear (d : ℕ) (p : Fin d → Prop) [DecidablePred p]
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, ¬ p i → (∀ k, p k → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i)
      (volume : Measure (Fin d → ℝ)) volume := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  have he_mp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p

  let G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ) := fun a i => f (e.symm (a, 0)) i
  have hG : Measurable G := by
    refine Measurable.of_eval (fun i => ?_)
    exact (measurable_pi_apply (i : Fin d)).comp
      (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))

  have hΨ : MeasurePreserving
      (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a)
      (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst))
      (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)
  have key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) =
      e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e := by
    funext x i
    have hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k := fun k hk => by simp [e, hk]
    by_cases hi : p i
    · simp [e, hi]
    · simp [e, G, hi, h x _ i hi hx]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)

theorem measurePreserving_triangular_shear (d : ℕ) (deg : Fin d → ℕ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by

  let U : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun n x i => if n ≤ deg i then x i + f x i else x i
  have hS : ∀ n, MeasurePreserving
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume :=
    fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf
      (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))
  have hstep : ∀ n, U n =
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1) := by
    intro n
    funext x i
    by_cases hin : deg i = n
    · have hfx : f (U (n + 1) x) i = f x i :=
        h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])
      simp only [Function.comp_apply, hfx]
      simp only [U]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.comp_apply, U]
      rw [if_pos hin]
      by_cases h2 : n ≤ deg i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hN : ∀ n, Finset.univ.sup deg < n → U n = id := by
    intro n hn
    funext x i
    have hi : deg i ≤ Finset.univ.sup deg := Finset.le_sup (Finset.mem_univ i)
    simp only [U, id]
    rw [if_neg (by omega)]
  have hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [hN n (by omega)]
      exact MeasurePreserving.id _
    | succ k ih =>
      intro n hn
      rw [hstep n]
      exact (hS n).comp (ih (n + 1) (by omega))
  have h0 : U 0 = fun x => x + f x := by
    funext x i
    simp [U]
  rw [← h0]
  exact hU (Finset.univ.sup deg + 1) 0 (by omega)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShearStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.measurePreserving_add_of_triangular : ∀ (d : ℕ) (deg : Fin d → ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)), Measurable f → (∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) → MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by
  first | exact @GlobalTheory.measurePreserving_triangular_shear | exact GlobalTheory.measurePreserving_triangular_shear | (intros; apply GlobalTheory.measurePreserving_triangular_shear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroupStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup : ∀ (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (E i)) → ∀ g : Formalism.REAL.UJ ε, (uMat g - 1) - Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε ∈ Submodule.span ℝ (Set.range E) → ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ Formalism.REAL.hs (uMat g - 1) ∧ Formalism.REAL.hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + Formalism.REAL.hs (uMat g - 1) ^ 2 / 4 := by
  first | exact @GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | exact GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | (intros; apply GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotent

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool} {d : ℕ}

theorem continuous_uMat_sub_one : Continuous fun g : UJ ε => uMat g - 1 :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem continuous_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1) :=
  continuous_pi fun i => (ipL (E i)).continuous_of_finiteDimensional.comp continuous_uMat_sub_one

theorem continuous_hs_sub_one : Continuous fun g : UJ ε => hs (uMat g - 1) := by
  unfold hs
  fun_prop

theorem mul_sub_one (g h : UJ ε) :
    uMat (g * h) - 1 = (uMat g - 1) + (uMat h - 1) + (uMat g - 1) * (uMat h - 1) := by
  have : uMat (g * h) = uMat g * uMat h := rfl
  rw [this]; noncomm_ring

theorem measurePreserving_coord {m : ℕ} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}
    (hle : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {ν : Measure (UJ ε)} (hν : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ν) :
    MeasurePreserving (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ν volume := by
  have hE0 : ∀ i, E i ∈ A 0 ∧ inG ε (E i) := fun i =>
    (hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hsp0 : ∀ X, (X ∈ A 0 ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := fun X => by
    simpa using hsp 0 X
  have hmul0 : ∀ X ∈ A 0, ∀ Y ∈ A 0, X * Y ∈ A 0 := fun X hX Y hY => hle 0 (hmul 0 X hX Y hY).1
  obtain ⟨σ, hσc, hσ⟩ := GlobalTheory.T.exists_orthonormal_lie_coordinates n d m ε A E hm hmul hle hinv hE hE0
  have hσ2 : ∀ x i, ipL (E i) (uMat (σ x) - 1) = x i := fun x => (hσ x).2
  have hinj : ∀ g h : UJ ε, uMat g - 1 ∈ A 0 → uMat h - 1 ∈ A 0 →
      (∀ i, ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) → g = h := by
    intro g h hg hh hc
    have := sub_mem_of_coord_eq hmul hinv hE hsp hg hh m fun i _ => hc i
    rw [hm, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext (Units.ext this)
  have hS : MeasurableSet {g : UJ ε | uMat g - 1 ∈ A 0} :=
    ((A 0).closed_of_finiteDimensional.preimage continuous_uMat_sub_one).measurableSet
  have hμ : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ((volume : Measure (Fin d → ℝ)).map σ) := by
    refine ⟨?_, fun s hs => ?_, ?_⟩
    · rw [Measure.map_apply hσc.measurable hS.compl]
      convert measure_empty (μ := (volume : Measure (Fin d → ℝ)))
      ext x
      simpa using (hσ x).1
    · have hs' : uMat s - 1 ∈ A 0 := hs
      have hT := GlobalTheory.T.measurePreserving_add_of_triangular d deg (fun x i => ipL (E i) (uMat (s * σ x) - 1) - x i)
        (((continuous_coord E).comp (continuous_const.mul hσc)).sub continuous_id).measurable (by
          intro x y i hxy
          have h1 := sub_mem_of_coord_eq hmul hinv hE hsp (hσ x).1 (hσ y).1 (deg i) fun k hk => by
            rw [hσ2, hσ2, hxy k hk]
          have h2 := ipL_eq_zero_of_mem hE (fun i => (hE0 i).2) (hinv (deg i + 1))
            (fun X => (hsp (deg i + 1) X).1) (i := i) (by simp) (hmul _ _ h1 _ hs').2
          have h3 : (uMat s - 1) * (uMat (σ x) - uMat (σ y)) =
              (uMat s - 1) * (uMat (σ x) - 1) - (uMat s - 1) * (uMat (σ y) - 1) := by noncomm_ring
          rw [h3, map_sub] at h2
          simp only [mul_sub_one, map_add (f := _), hσ2]
          linarith)
      have he : (fun g => s * g) ∘ σ =
          σ ∘ fun x => x + fun i => ipL (E i) (uMat (s * σ x) - 1) - x i := by
        funext x
        refine hinj _ _ ?_ (hσ _).1 fun i => ?_
        · simp only [Function.comp, mul_sub_one]
          exact (A 0).add_mem ((A 0).add_mem hs' (hσ x).1) (hmul0 _ hs' _ (hσ x).1)
        · simp only [Function.comp, hσ2, Pi.add_apply]
          ring
      rw [Measure.map_map (measurable_const_mul s) hσc.measurable, he,
        ← Measure.map_map hσc.measurable hT.measurable, hT.map_eq]
    · have hest := fun x => GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup n d ε E hE (fun i => (hE0 i).2) (σ x)
        ((hsp0 _).1 ⟨(A 0).sub_mem (hσ x).1 (hinv 0 _ (hσ x).1), inG_sub_inv _⟩)
      simp only [(hσ _).2] at hest
      have h0 : σ 0 = 1 := hinj _ _ (hσ 0).1 (by simp [uMat]) fun i => by
        rw [hσ2]; simp [uMat]
      have := GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball d (fun x => hs (uMat (σ x) - 1))
        (continuous_hs_sub_one.comp hσc).continuousAt (by simp [h0, uMat, hs])
        (fun x => (hest x).1) (fun x => (hest x).2)
      refine this.congr fun r => ?_
      rw [Measure.map_apply hσc.measurable
        (isClosed_le continuous_hs_sub_one.sqrt continuous_const).measurableSet]
      rfl
  have heq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε (A 0) d E hmul0 hE hsp0 ν hν).2.2.1 _ hμ
  refine ⟨(continuous_coord E).measurable, ?_⟩
  rw [← heq, Measure.map_map (continuous_coord E).measurable hσc.measurable]
  have : (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ∘ σ = id := by
    funext x i
    exact hσ2 x i
  rw [this, Measure.map_id]

theorem covol_le_prod_layers : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ n d m ε A E deg hle hm hmul hinv hE hsp ν _ hν Γ D hΓ hD hcov
  have hE0 : ∀ v i, E v i ∈ A v 0 ∧ inG (ε v) (E v i) := fun v i =>
    (hsp v 0 (E v i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hanti : ∀ v, Antitone (A v) := fun v => antitone_nat_of_succ_le (hle v)
  have horth : ∀ v c i, deg i < c → ∀ X ∈ A v c, ipL (E v i) X = 0 := fun v c i hi X hX =>
    ipL_eq_zero_of_mem (hE v) (fun i => (hE0 v i).2) (hinv v c) (fun X => (hsp v c X).1)
      (by simpa using hi) hX
  have hdeg : ι → ∀ i, deg i < m := by
    intro v i
    by_contra hi
    have h1 := ((hsp v m (E v i)).2 (Submodule.subset_span ⟨i, not_lt.1 hi, rfl⟩)).1
    rw [hm, Submodule.mem_bot] at h1
    have := hE v i i
    simp [h1] at this
  have hmp := measurePreserving_pi ν (fun _ => (volume : Measure (Fin d → ℝ))) fun v =>
    measurePreserving_coord (hle v) (hm v) (hmul v) (hinv v) (hE v) (hsp v) (hν v)
  have hB : MeasurableSet {x : ι → Fin d → ℝ |
      ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (show Measurable fun (x : ι → Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => x v i.1 by
      fun_prop) (hD c)
  rw [← GlobalTheory.T.volume_product_over_grading_layers ι d m deg D hdeg hD]
  refine le_trans ?_ (hmp.measure_preimage hB.nullMeasurableSet).le
  refine iInf_le_of_le _ (iInf_le_of_le (hmp.measurable hB) (iInf_le_of_le ?_ le_rfl))
  intro x hx
  have key : ∀ k : ℕ, ∃ γ ∈ Γ, (∀ v, uMat ((γ * x) v) - 1 ∈ A v 0) ∧ ∀ c < k,
      (fun v (i : {i : Fin d // deg i = c}) => ipL (E v i.1) (uMat ((γ * x) v) - 1)) ∈ D c := by
    intro k
    induction k with
    | zero => exact ⟨1, Γ.one_mem, by simpa using hx, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    | succ k ih =>
      obtain ⟨γ, hγ, h0, hc⟩ := ih
      obtain ⟨δ, hδ, hδk, hδD⟩ := hcov k fun v i => ipL (E v i.1) (uMat ((γ * x) v) - 1)
      have hexp : ∀ v, uMat ((δ * γ * x) v) - 1 = (uMat (δ v) - 1) + (uMat ((γ * x) v) - 1) +
          (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) := fun v => by
        rw [mul_assoc, Pi.mul_apply, mul_sub_one]
      have hprod : ∀ v, (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) ∈ A v (k + 1) := fun v =>
        (hmul v k _ (hδk v) _ (h0 v)).1
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, fun v => ?_, fun c hck => ?_⟩
      · rw [hexp]
        exact (A v 0).add_mem ((A v 0).add_mem (hΓ δ hδ v) (h0 v)) (hanti v (Nat.zero_le _) (hprod v))
      · rcases (Nat.lt_succ_iff.1 hck).lt_or_eq with h | rfl
        · convert hc c h using 1
          funext v i
          rw [hexp, map_add (f := _), map_add (f := _), horth v k i.1 (by rw [i.2]; exact h) _ (hδk v),
            horth v (k + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), zero_add, add_zero]
        · convert hδD using 1
          funext v i
          rw [hexp, map_add (f := _), map_add (f := _), horth v (c + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), add_zero]
          rfl
  obtain ⟨γ, hγ, -, hc⟩ := key m
  exact ⟨γ, hγ, hc⟩

end GlobalTheory.NilCov
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotentStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.covolume_le_prod_layers_unipotent : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  first | exact @GlobalTheory.NilCov.covol_le_prod_layers | exact GlobalTheory.NilCov.covol_le_prod_layers | (intros; apply GlobalTheory.NilCov.covol_le_prod_layers <;> assumption)
end
end
