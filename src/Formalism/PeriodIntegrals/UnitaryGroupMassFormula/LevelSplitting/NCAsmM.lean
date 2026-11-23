module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.FiniteAdelesSecondCountable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmV

section

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem map_eq_of_split (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  haveI := hμ
  set U : AddSubgroup V := p.ker with hUdef
  have hWc : IsClosed (W : Set V) := by
    have e : (W : Set V) = {v | p v = v} := Set.ext fun v => hW v
    rw [e]
    exact isClosed_eq hp continuous_id
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = {v | p v = 0} := Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]
    rw [e]
    exact isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace W := hWc.locallyCompactSpace
  haveI : LocallyCompactSpace U := hUc.locallyCompactSpace
  haveI : BorelSpace W := Subtype.borelSpace (fun x => x ∈ (W : Set V))
  haveI : BorelSpace U := Subtype.borelSpace (fun x => x ∈ (U : Set V))
  haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)
  haveI : BorelSpace (W × U) := Prod.borelSpace
  have hpW : ∀ w : W, p w = w := fun w => (hW w).1 w.2
  have hfc : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V) := funext hf
    rw [e]
    exact hg.comp continuous_subtype_val
  let Φ : W × U →+ V := W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)
  have hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V) := fun x => rfl
  have hΦc : Continuous Φ := by
    have e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V) := funext hΦ
    rw [e]
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  let Ψ : V → W × U := fun v => (⟨p v, (hW _).2 (hpp v)⟩,
    ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)
  have hΨc : Continuous Ψ :=
    (hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by
      simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp])
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by
    rw [hΦ]
    simp [Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    rintro ⟨w, u⟩
    have hu : p u = 0 := u.2
    have hpx : p (Φ (w, u)) = w := by rw [hΦ, map_add (f := _), hpW, hu, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      show p (Φ (w, u)) = w
      exact hpx
    · apply Subtype.ext
      show Φ (w, u) - p (Φ (w, u)) = u
      rw [hpx, hΦ]
      simp
  have hΦs : Function.Surjective Φ := fun v => ⟨Ψ v, hΦΨ v⟩
  let e : (W × U) ≃ₜ V :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦc, continuous_invFun := hΨc }
  let ν : Measure U := Measure.addHaar
  set P : Measure (W × U) := μ.prod ν with hP
  haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance
  have hHaar : (P.map Φ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact
  have hmap := hV _ hHaar
  have hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id := by
    funext x
    obtain ⟨w, u⟩ := x
    simp only [Function.comp, Prod.map, id, hΦ, map_add (f := _), hgU u u.2, hf]
  have hfm : Measurable f := hfc.measurable
  have hPm : Measurable (Prod.map f (id : U → U)) := hfm.prodMap measurable_id
  rw [Measure.map_map hg.measurable hΦc.measurable, hgΦ,
    ← Measure.map_map hΦc.measurable hPm] at hmap
  have hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q := by
    intro Q
    rw [Measure.map_map hΨc.measurable hΦc.measurable]
    have e2 : Ψ ∘ Φ = id := funext hΨΦ
    rw [e2, Measure.map_id]
  have hP' : P.map (Prod.map f id) = P := by
    have h2 := congrArg (fun Q => Q.map Ψ) hmap
    simpa only [hinv] using h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (0 : U)
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  ext A hA
  rw [Measure.map_apply hfm hA]
  have h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K) := by rw [hP']
  rw [Measure.map_apply hPm (hA.prod hKc.measurableSet)] at h1
  have hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K := by
    ext x
    simp
  rw [hpre, hP, Measure.prod_prod, Measure.prod_prod] at h1
  have h2 := congrArg (fun t => t / ν K) h1
  simp only [ENNReal.mul_div_cancel_right hK0 hKt] at h2
  exact h2

end Gen

namespace DatL

open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}

theorem h_e_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (D.pXv v) = D.h (D.e b) v := by

  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ef, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pX (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pX v) = D.h (D.f b) v := by
  have hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0 := by
    intro a
    rw [Dat.h_symm H (D.e a) (D.f b), H.ef]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

  rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pXv v) = 0 := by

  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero,
    Finset.sum_const_zero]


variable (D) in
def pL : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

theorem pL_apply (v : n → A) : pL D v = v - D.pX v - D.pXv v := rfl

theorem h_e_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (pL D v) = 0 := by
  have h0 : D.h (D.e b) (D.pX v) = 0 := by

    rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero,
      Finset.sum_const_zero]
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h0, h_e_pXv H]
  ring

theorem h_f_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (pL D v) = 0 := by
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h_f_pX H, h_f_pXv H]
  ring

theorem pL_of {v : n → A} (he : ∀ a, D.h (D.e a) v = 0) (hf : ∀ a, D.h (D.f a) v = 0) :
    pL D v = v := by
  have h1 : D.pX v = 0 := by
    simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, hf, zero_smul,
      Finset.sum_const_zero]
  have h2 : D.pXv v = 0 := by
    simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, he, zero_smul,
      Finset.sum_const_zero]
  rw [pL_apply, h1, h2, sub_zero, sub_zero]

theorem pL_pL (H : D.Hyp) (v : n → A) : pL D (pL D v) = pL D v :=
  pL_of (fun a => h_e_pL H a v) (fun a => h_f_pL H a v)

theorem fix_of_pL_zero {S : (n → A) →ₗ[A] (n → A)} (hSe : ∀ a, S (D.e a) = D.e a)
    (hSf : ∀ a, S (D.f a) = D.f a) {u : n → A} (hu : pL D u = 0) : S u = u := by
  have hu' : u = D.pX u + D.pXv u := by
    rw [pL_apply, sub_sub, sub_eq_zero] at hu
    exact hu
  rw [hu', map_add (f := _)]
  congr 1

  · simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]

  · simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]

end DatL

section Wp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem mem_Wp_iff (H : (datR R σ J P T).Hyp) (v : Fin M → R ⊗[F] E) :
    v ∈ Wp R σ J P ↔ DatL.pL (datR R σ J P T) v = v := by
  constructor
  · rintro ⟨he, hf⟩
    exact DatL.pL_of (fun a => he a) (fun a => hf a)
  · intro h
    change (∀ a, _) ∧ (∀ a, _)
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have h1 := DatL.h_e_pL H a v
      rw [h] at h1
      exact h1
    · have h1 := DatL.h_f_pL H a v
      rw [h] at h1
      exact h1

theorem lin_mem_Wp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ Wp R σ J P) : lin R σ J h w ∈ Wp R σ J P := by
  obtain ⟨he, hf⟩ := hw
  have hfix : ∀ i, lin R σ J h (ratV (F := F) R (tupH P i)) = ratV (F := F) R (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  change (∀ a, _) ∧ (∀ a, _)
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    rw [← h1, hR_lin]
    exact he a
  · have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    rw [← h1, hR_lin]
    exact hf a

def linWp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : Wp R σ J P) : Wp R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wp hh w.2⟩

end Wp

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem sc_tens : SecondCountableTopology (Af F ⊗[F] E) := by
  haveI := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  infer_instance

theorem wp_map (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) {h : HA (Af F) σ J} (hh : h ∈ Hsub (Af F) σ J P)
    (μ : Measure (Wp (Af F) σ J P)) (hμ : μ.IsAddHaarMeasure) : μ.map (linWp hh) = μ := by
  haveI := sc_tens (F := F) (E := E)
  have H := datR_hyp (R := Af F) hσσ hJ hP
  have hfix : ∀ i, lin (Af F) σ J h (ratV (F := F) (Af F) (tupH P i)) = ratV (F := F) (Af F) (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  have hSe : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).e a) = (datR (Af F) σ J P T).e a := by
    intro a
    have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    exact h1
  have hSf : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).f a) = (datR (Af F) σ J P T).f a := by
    intro a
    have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    exact h1
  refine map_eq_of_split (DatL.pL (datR (Af F) σ J P T)).toAddMonoidHom ?_
    (fun v => DatL.pL_pL H v) (Wp (Af F) σ J P) (fun v => mem_Wp_iff H v)
    (lin (Af F) σ J h).toAddMonoidHom ?_ (fun u hu => DatL.fix_of_pL_zero hSe hSf hu)
    (fun ν hν => hV hJ hσσ h ν hν) (linWp hh) (fun w => rfl) μ hμ
  · exact LinearMap.continuous_on_pi _
  · exact LinearMap.continuous_on_pi _

end Af

end PI.LevelKSplit.W.NCA
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds

section

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

theorem subgroup_locally_compact_holds : SubLCSC := by
  intro X _ _ Γ K hX hK hΓc hΓd
  obtain ⟨hlc, hsc, ht2, htg⟩ := hX
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := htg
  haveI := hΓc
  haveI := hΓd
  let f : ratG Γ K → Γ := fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩
  refine ⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology,
    inferInstance, inferInstance⟩, ?_, ?_⟩
  · have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg (fun y : Γ => (y : X)) h
      exact h'
    exact hf.countable
  · have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hemb : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hcont continuous_subtype_val
      show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology

end PI.VolSemiDirect.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmM

section

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | PI.LevelKSplit.W.NCA.DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
end
end
end
