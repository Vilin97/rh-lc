module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_map_of_unramified (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu, Ideal.top_mul]

theorem dInv_eq_inv_coe (K : Type) [Field K] [NumberField K] (j : ℕ) :
    dInv K j = ((↑(differentIdeal ℤ (𝓞 K) ^ j) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [dInv, FractionalIdeal.coeIdeal_pow, inv_pow]

theorem algebraMap_mem_inv_map_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (y : F) :
    algebraMap F E y ∈ ((↑(I.map (algebraMap (𝓞 F) (𝓞 E))) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔
      y ∈ ((↑I : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have hIE : I.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hIE),
    FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)]
  have key : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) =
      algebraMap F E (algebraMap (𝓞 F) F a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have h1 := h (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a))
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_map_of_mem _ ha, rfl⟩)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [key, ← map_mul] at hc
    have hint : IsIntegral ℤ (y * algebraMap (𝓞 F) F a) := by
      rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
      show IsIntegral ℤ (algebraMap F E (y * algebraMap (𝓞 F) F a))
      rw [← hc]
      exact c.2
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    let T : Ideal (𝓞 E) := Submodule.comap
      ((LinearMap.mulLeft (𝓞 E) (algebraMap F E y)) ∘ₗ Algebra.linearMap (𝓞 E) E)
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) ≤ T := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩))
      show algebraMap F E y * algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) ∈
        (1 : FractionalIdeal (𝓞 E)⁰ E)
      rw [key, ← map_mul, ← hc]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨algebraMap (𝓞 F) (𝓞 E) c, key c⟩
    exact hle hb

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

theorem imV_eq_zero_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : imV x = 0 ↔ σ x = x := by
  constructor
  · intro hx
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    let w : InfinitePlace E := InfinitePlace.mk τ
    have him : (w.embedding x).im = 0 := congrFun hx w
    apply w.embedding.injective
    rw [h.2.2.2]
    exact Complex.conj_eq_iff_im.2 him
  · intro hx
    funext w
    show (w.embedding x).im = 0
    have := h.2.2.2 w.embedding x
    rw [hx] at this
    exact Complex.conj_eq_iff_im.1 this.symm

end Fixed

theorem mem_dInv_imV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
    ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  intro F E _ _ _ _ _ σ h hu j x
  have hIne : differentIdeal ℤ (𝓞 F) ^ j ≠ ⊥ := pow_ne_zero _ differentIdeal_ne_bot
  have hE : dInv E j = ((↑((differentIdeal ℤ (𝓞 F) ^ j).map (algebraMap (𝓞 F) (𝓞 E))) :
      FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [dInv_eq_inv_coe, differentIdeal_eq_map_of_unramified hu, Ideal.map_pow]
  constructor
  · rintro ⟨hx, him⟩
    obtain ⟨y, rfl⟩ := mem_range_of_cm_fixed h ((imV_eq_zero_iff h x).1 him)
    refine ⟨y, ?_, rfl⟩
    rw [dInv_eq_inv_coe]
    rw [hE] at hx
    exact (algebraMap_mem_inv_map_iff _ hIne y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (imV_eq_zero_iff h _).2 (σ.commutes y)⟩
    rw [hE]
    rw [dInv_eq_inv_coe] at hy
    exact (algebraMap_mem_inv_map_iff _ hIne y).2 hy

end GlobalTheory.SnMass.SkewVol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hc.2.2.2 τ, hc.2.2.2 τ, star_star]

theorem exists_anti_unit {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {v : Pl (F := F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (τ : E →ₐ[F] Fv F v) (δ : 𝓞 E), σ (δ : E) = -(δ : E) ∧ Valued.v (τ (δ : E)) = 1 := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hPv : P.under (𝓞 F) = v := HeightOneSpectrum.ext hP
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv
  obtain ⟨w', hne, -, -, -, hw'⟩ := SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩
  have hmax : (splitPrime τ).asIdeal.IsMaximal := (splitPrime τ).isMaximal
  have hmax' : w'.asIdeal.IsMaximal := w'.isMaximal
  have hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))
  obtain ⟨θ, hθP, hθw⟩ := Set.not_subset.1 hnle
  set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ
  have hσθP : σθ ∉ (splitPrime τ).asIdeal := by
    intro h
    apply hθw
    rw [hw']
    exact h
  refine ⟨τ, θ - σθ, ?_, ?_⟩
  · have e : ((σθ : 𝓞 E) : E) = σ (θ : E) := rfl
    push_cast
    rw [map_sub]
    change σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))
    rw [conj_conj hc]
    ring
  · have hnot : θ - σθ ∉ (splitPrime τ).asIdeal := by
      intro h
      apply hσθP
      have := (splitPrime τ).asIdeal.sub_mem hθP h
      simpa using this
    rw [mem_splitPrime] at hnot
    exact le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)

theorem smul_eq_self_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M}
    (hz : At (evFin F v) z) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftV_mul_liftV (v : Pl (F := F)) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = GlobalTheory.LatVac.liftV v (a * b) := by
  rw [show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]
  show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _
  rw [GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.SplitSign


open GlobalTheory.SplitSign in
theorem GlobalTheory.SplitSign.exists_split_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨τ, δ, hσδ, hδv⟩ := exists_anti_unit hB.cm hv
  set s : Fv F v := τ (δ : E) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hδv
    exact zero_ne_one hδv
  have hsinv : s⁻¹ ∈ v.adicCompletionIntegers F := by
    show Valued.v s⁻¹ ≤ 1
    rw [map_inv₀, hδv, inv_one]
  obtain ⟨f, hf⟩ := SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ)
    (by rw [map_mul, hσδ, neg_mul_neg])
  refine ⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩
  · rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]
  · intro u hu
    rw [TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]
  · intro z hz
    have hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) =
        GlobalTheory.LatVac.liftV v 1 • (1 : AE F E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]
      have h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v) := by
        rw [Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]
        field_simp
      rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]
  · intro d W z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem hsinv hav
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitSign.exists_split_sign | exact GlobalTheory.SplitSign.exists_split_sign | (intros; apply GlobalTheory.SplitSign.exists_split_sign <;> assumption)
end
end
