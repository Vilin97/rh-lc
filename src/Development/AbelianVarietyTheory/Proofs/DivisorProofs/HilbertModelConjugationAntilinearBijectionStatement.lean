module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeSobolevBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear

-- Source module: Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.SubsingletonOfEvInj

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem evAt_injective_of_ne {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : ∀ τ, (v τ : (R.MW i σ).H τ) ≠ 0) : Function.Injective (evAt R i σ v) := by
  intro x y hxy
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [map_sub]
    show (R.HW i σ).e x v - (R.HW i σ).e y v = 0
    exact sub_eq_zero.2 hxy
  have hip : ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) = 0 := by
    by_cases h : ∃ c, IsMultIP (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) c
    · have h1 := (ipM_spec _ _ _ _ _ h v v).2
      rw [h0] at h1
      simp only [Pi.zero_apply, mul_zero, integral_zero] at h1
      rcases mul_eq_zero.1 h1.symm with h2 | h2
      · exact h2
      · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h2
        exact absurd (inner_self_eq_zero.1 hτ) (hv τ)
    · unfold ipM
      rw [dite_eq_right h]
  have h3 := (hm i σ).2.2 (x - y) (x - y)
  unfold ipAt at h3
  rw [hip, mul_zero] at h3
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end GlobalTheory.EvalInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeSobolevBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_antiunitary_intertwiner_conjugateEmbedding_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i ((starRingEnd ℂ).comp σ)).H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ y, c τ ((R.MW i σ).rep τ g y) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (c τ y) := by
  first | exact @GlobalTheory.ConjEq.exists_conj_equiv | exact GlobalTheory.ConjEq.exists_conj_equiv | (intros; apply GlobalTheory.ConjEq.exists_conj_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijection

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjHilb

theorem nonempty_antilinear {H H' Y : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev) (hinj' : Function.Injective ev')
    (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (hy : ∀ x, ∃ y, ∀ g, ev y g = starRingEnd ℂ (ev' x g)) :
    Nonempty (H' ≃ₗ⋆[ℂ] H) := by
  choose x hx using hx
  choose y hy using hy
  exact ⟨{ toFun := y
           invFun := x
           map_add' := fun a b => hinj (funext fun g => by rw [ha, hy, hy, hy, ha', map_add (f := _)])
           map_smul' := fun z a => hinj (funext fun g => by rw [hs, hy, hy, hs', map_mul])
           left_inv := fun a => hinj' (funext fun g => by rw [hx, hy, Complex.conj_conj])
           right_inv := fun a => hinj (funext fun g => by rw [hy, hx, Complex.conj_conj]) }⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_conj_value (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ σ' : D.what₂.LL →+* ℂ)
    (c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i σ').H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ w, c τ ((R.MW i σ).rep τ g w) = (R.MW i σ').rep τ g (c τ w))
    (v : (R.MW i σ).Vec) (v' : (R.MW i σ').Vec) (hv : ∀ τ, (v' τ : (R.MW i σ').H τ) = c τ (v τ)) (y : (R.HW i σ').H) :
    ∃ x : (R.HW i σ).H, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i σ' v' y g) := by
  obtain ⟨-, hmul⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i σ') (R.MW i σ) c hc
  have hχ : (fun k => star (levChi _ (R.βW i) (R.datWp i R.triv) k)) = levChi _ (R.βW i) (R.datWp i R.triv) := by
    funext k
    rw [GlobalTheory.ConjEval.levChi_principal, star_one]
  have h1 : (R.HW i σ').e y ∈ R.Wall i σ' := (hm i _).2.1 ▸ LinearMap.mem_range_self _ y
  obtain ⟨T', hT', h2⟩ := hmul _ _ _ h1
  rw [hχ] at hT'
  obtain ⟨x, rfl⟩ : T' ∈ LinearMap.range (R.HW i σ).e := (hm i σ).2.1.symm ▸ hT'
  exact ⟨x, h2 v _ hv⟩

theorem evAt_inj (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : IsUnitV v) : Function.Injective (evAt R i σ v) :=
  GlobalTheory.EvalInj.evAt_injective_of_ne R hm i σ v fun τ h => by
    have := hv τ
    rw [h, norm_zero] at this
    exact zero_ne_one this

theorem conj_hilbert : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → (∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → Nonempty ((R.HW i σ).H ≃ₗ⋆[ℂ] (R.HW i ((starRingEnd ℂ).comp σ)).H)) ∧ (JEvExists T R κ v₀ → JEvBar T R κ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hm := hM.HW
  have hadd : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) a b g,
      evAt R i σ' u (a + b) g = evAt R i σ' u a g + evAt R i σ' u b g := fun i σ' u a b g => by
    simp [evAt]
  have hsmul : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) (z : ℂ) a g,
      evAt R i σ' u (z • a) g = z * evAt R i σ' u a g := fun i σ' u z a g => by
    simp [evAt]
  have key : ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ v : (R.MW i σ).Vec, IsUnitV v ∧
      (∀ y, ∃ x, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g)) ∧
      ∀ x, ∃ y, ∀ g, evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g = starRingEnd ℂ (evAt R i σ v x g) := by
    intro i σ hσ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_antiunitary_intertwiner_conjugateEmbedding_models D G Pl0 T0 A T R κ v₀ hM ht i σ hσ
    obtain ⟨hsm, -⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i ((starRingEnd ℂ).comp σ)) (R.MW i σ) c hc
    let v : (R.MW i σ).Vec := fun τ => ⟨(c τ).symm (v₀ i ((starRingEnd ℂ).comp σ) τ), (hsm τ _).2 (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact (v₀ i ((starRingEnd ℂ).comp σ) τ).2)⟩
    refine ⟨v, fun τ => ((c τ).symm.norm_map _).trans ((ht.hv₀ i _).norm R τ),
      exists_conj_value R hm i σ _ c hc v _ fun τ => ((c τ).apply_symm_apply _).symm,
      exists_conj_value R hm i _ σ (fun τ => (c τ).symm) (fun τ g hg w => (c τ).injective ?_) _ v fun τ => rfl⟩
    rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply]
  refine ⟨fun i σ hσ => ?_, fun hJ i σ hσ hV => ?_⟩
  · obtain ⟨v, hv, hx, hy⟩ := key i σ hσ
    exact nonempty_antilinear _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i _ _ fun τ => (ht.hv₀ i _).norm R τ) (evAt_inj R hm i σ v hv) hx hy
  · obtain ⟨v, hv, hx, -⟩ := key i σ hσ
    exact ⟨v, hv, GlobalTheory.ConjEval.evEx_conj (res T σ) _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i σ v hv) hx _ (hJ i ((starRingEnd ℂ).comp σ) (good_resC T hσ) hV)⟩

end GlobalTheory.ConjHilb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijectionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → (∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → Nonempty ((R.HW i σ).H ≃ₗ⋆[ℂ] (R.HW i ((starRingEnd ℂ).comp σ)).H)) ∧ (JEvExists T R κ v₀ → JEvBar T R κ) := by
  first | exact @GlobalTheory.ConjHilb.conj_hilbert | exact GlobalTheory.ConjHilb.conj_hilbert | (intros; apply GlobalTheory.ConjHilb.conj_hilbert <;> assumption)
end
end
