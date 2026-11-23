module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MapEqOfSmul
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsNeOfSurjOn
import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLatticeOf
public import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.ChiIndep

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac

namespace PositivityTheory.ThKF0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem chi_indep (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {θ θ' : 𝓞 E} (h : (θ : E) + σ θ = 1)
    (h' : (θ' : E) + σ θ' = 1) {v : Pl (F := F)} {γ} (hγ : γ ∈ latAtV X W v) :
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  have h0 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1 (by rw [map_one]; exact one_mem _)
    γ hγ γ hγ
  rw [← mul_one (B.ψ (_ * symp _ (inclR (F := F) (AF F) (θ' : E)) _ _ _ _)), ← h0, ← AddChar.map_add_eq_mul]
  congr 1
  have hc := PositivityTheory.ThK.Vac.cA_cA (PositivityTheory.ThK.Vac.sigma_sigma hB.cm)
  have hh := GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (JA := incM F X.J) (JB := incM F W.J) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hX.herm]) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = -inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hW.skew, map_neg]) γ γ
  have e1 : cA σ (inclR (F := F) (AF F) (θ : E)) = 1 - inclR (F := F) (AF F) (θ : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h, map_sub, map_one]
  have e2 : cA σ (inclR (F := F) (AF F) (θ' : E)) = 1 - inclR (F := F) (AF F) (θ' : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h', map_sub, map_one]
  simp only [symp, one_mul]
  rw [show ((θ * (θ - θ') : 𝓞 E) : E) = θ * (θ - θ') by simp, map_mul (inclR (F := F) (AF F)), map_sub (inclR (F := F) (AF F))]
  generalize hTens (cA σ) (incM F X.J) (incM F W.J) γ γ = T at hh ⊢
  generalize inclR (F := F) (AF F) (θ : E) = a at e1 ⊢
  generalize inclR (F := F) (AF F) (θ' : E) = a' at e2 ⊢
  have t := GlobalTheory.VacCocycle.trace_conj (R := AF F) (cA σ) hc (a * (a - a') * T)
  rw [map_mul (cA σ), map_mul (cA σ), map_sub (cA σ), e1, e2, hh, show (1 - a) * (1 - a - (1 - a')) * -T = a * T - a' * T - a * (a - a') * T by ring,
    map_sub, map_sub] at t
  have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = u at h3 ⊢
  change u * Algebra.trace (AF F) (AE F E) (a * T) =
    u * Algebra.trace (AF F) (AE F E) (a' * T) + Algebra.trace (AF F) (AE F E) (a * (a - a') * T)
  linear_combination u * t + (Algebra.trace (AF F) (AE F E) (a * (a - a') * T)) * h3

theorem loc_eig {ψ : AddChar (AF F) ℂ} (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    {v : Pl (F := F)} {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) {γ} (hγ : γ ∈ latAtV X W v) {c : ℂ}
    (h : Acts (evFin F v) (co.rho ψ γ) φ (c • φ)) : schr (psiAt ψ v) (locCo co v γ) φ = c • φ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun t ht =>
    (GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ ((latAtV_at_stable X W v).1 γ hγ) φ t ht).symm.trans (h t ht)

theorem vac_line (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W) (v : Pl (F := F)) {φ φ'}
    (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') : ∃ c : ℂ, c ≠ 0 ∧ φ' = c • φ := by
  obtain ⟨hs, h0, θ, hθ, hA⟩ := h
  obtain ⟨hs', h0', θ', hθ', hA'⟩ := h'
  obtain ⟨c, hc⟩ := PositivityTheory.ThK.Vac.local_line M.co hB.std v (latAtV X W v) (latAtV_at_stable X W v).1
    (fun z hz h => PositivityTheory.ThK.Vac.mem_latAtV hB hX hW v hz h) _ hs hs' h0 (fun γ hγ => loc_eig M.co hs hγ (hA γ hγ))
    fun γ hγ => by
      have k := loc_eig M.co hs' hγ (hA' γ hγ)
      rw [← chi_indep hB hX hW hθ hθ' hγ] at k
      exact k
  exact ⟨c, fun c0 => h0' (by rw [hc, c0, zero_smul]), hc⟩

end PositivityTheory.ThKF0

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.ModelChangeOf

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem exists_linearEquiv_of_rational {K R E α β κ : Type} [Field K] [CommRing R] [Algebra K R] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Fintype α] [Fintype β] [Fintype κ]
    (hinj : Function.Injective (algebraMap K R))
    (e : Matrix α β (R ⊗[K] E) ≃ₗ[R] (κ → R) × (κ → R))
    (h : ∀ x : Matrix α β E, ∃ y z : κ → K, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R (y i), fun i => algebraMap K R (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[K] (κ → K) × (κ → K), ∀ x, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R ((d₀ x).1 i), fun i => algebraMap K R ((d₀ x).2 i)) := by
  classical
  haveI : Nontrivial R := hinj.nontrivial
  choose y z hyz using h
  have hadd : ∀ a b : Matrix α β E, ((a + b).map fun t => (1 : R) ⊗ₜ[K] t) =
      (a.map fun t => (1 : R) ⊗ₜ[K] t) + b.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro a b
    ext i j
    simp [TensorProduct.tmul_add]
  have hsmul : ∀ (c : K) (a : Matrix α β E), ((c • a).map fun t => (1 : R) ⊗ₜ[K] t) =
      algebraMap K R c • a.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro c a
    ext i j
    change (1 : R) ⊗ₜ[K] (c • a i j) = algebraMap K R c • ((1 : R) ⊗ₜ[K] a i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let f : Matrix α β E →ₗ[K] (κ → K) × (κ → K) :=
    { toFun := fun x => (y x, z x)
      map_add' := by
        intro a b
        have key := hyz (a + b)
        rw [hadd, map_add (f := _), hyz a, hyz b] at key
        have h1 : ∀ i, algebraMap K R (y a i) + algebraMap K R (y b i) = algebraMap K R (y (a + b) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R (z a i) + algebraMap K R (z b i) = algebraMap K R (z (a + b) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (a + b) i) = algebraMap K R (y a i + y b i)
          rw [map_add (f := _), h1]
        · change algebraMap K R (z (a + b) i) = algebraMap K R (z a i + z b i)
          rw [map_add (f := _), h2]
      map_smul' := by
        intro c a
        have key := hyz (c • a)
        rw [hsmul, map_smul, hyz a] at key
        have h1 : ∀ i, algebraMap K R c * algebraMap K R (y a i) = algebraMap K R (y (c • a) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R c * algebraMap K R (z a i) = algebraMap K R (z (c • a) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (c • a) i) = algebraMap K R (c * y a i)
          rw [map_mul, h1]
        · change algebraMap K R (z (c • a) i) = algebraMap K R (c * z a i)
          rw [map_mul, h2] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : (a.map fun t => (1 : R) ⊗ₜ[K] t) = b.map fun t => (1 : R) ⊗ₜ[K] t :=
      e.injective (by rw [hyz a, hyz b, h1, h2])
    ext i j
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := R) (B := E) hinj (congrFun (congrFun h3 i) j)
  have hdim : Module.finrank K (Matrix α β E) = Module.finrank K ((κ → K) × (κ → K)) := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi, Module.finrank_baseChange] at h1
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi]
    simpa using h1
  refine ⟨LinearMap.linearEquivOfInjective f hf hdim, fun x => ?_⟩
  simpa [f] using hyz x

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem ratRel_of_good {ψ : AddChar (AF F) ℂ} {M M₁ : Model σ X W} (h : M.IsGood ψ) (h₁ : M₁.IsGood ψ) : RatRel M.co M₁.co := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d₀, hd⟩ := exists_linearEquiv_of_rational (AdeleRing.algebraMap_injective (𝓞 F) F) M.co.e h.rat
  intro y z
  obtain ⟨x, hx⟩ := d₀.surjective (y, z)
  obtain ⟨y', z', h'⟩ := h₁.rat x
  refine ⟨incM F x, y', z', ?_, h'⟩
  have := hd x
  rw [hx] at this
  exact this

end PositivityTheory.ThKF0

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.EvAdel

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem isEv_bij_of_adel (hA : PositivityTheory.Mix.AdelSt) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d} {M M₁ : Model σ X W} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) :
    ∃ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e ∧
      Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  classical
  have hψ := hB.std
  have hr := ratRel_of_good hM hM₁
  have hr' := ratRel_of_good hM₁ hM
  obtain ⟨e₁, ei, ev, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    PositivityTheory.Mix.darboux_model_rational_lattice_of hA F E σ B n d X W M r s r' s' hB hX hW hM M₁.co hM₁.rat
  choose c hc0 hc using fun v => vac_line hB hX hW M₁ v (hM₁.vac v) (φ' := ev v (M.vac v)) (hvac v)
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hM₁.std] with v h1 h2
    have h' := hc v
    rw [h1, h2] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n × Fin d → Fv F v) ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  have hfin0 : (Function.mulSupport c).Finite := Filter.eventually_cofinite.1 hc1
  have hk : (∏ᶠ v, c v)⁻¹ ≠ 0 := inv_ne_zero (finprod_ne_zero hc0)
  have hstd' : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hM.std] with v h1 h2
    rwa [h2] at h1
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := fun f φ h1 h2 =>
    hpure f φ h1 (by filter_upwards [h2, hM.std] with v e1 e2; rw [e1, e2])
  have hs := surjOn_of_pure e₁ ei ev hsurj (fun v => (hSB v).ge) hstd' hpure'
  have t₁ : Tw B.ψ M.co M₁.co e₁ := ⟨hmaps, hheis,
    Span.comp_mem_adm e₁ ei ev (fun v φ hφ => hSB v ▸ Submodule.mem_map_of_mem hφ) hstd' hpure', exists_ne_of_surjOn hs⟩
  have t := t₁.smul hk
  obtain ⟨e₀, t₀⟩ := twEx hA F B.ψ hψ _ _ _ M₁.co M.co
  obtain ⟨e', t', hl1, hl2⟩ := t.exists_inv hψ t₀ hr hr'
  refine ⟨_, ⟨t.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u), ei, fun v => (c v)⁻¹ • ev v, ?_, ?_, ?_⟩,
    ⟨t.maps, fun x hx y hy hxy => ?_, fun Φ hΦ => ⟨e' Φ, t'.maps Φ hΦ, hl2 Φ hΦ⟩⟩⟩
  · have h1 : ∀ m, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    exact t.Heisenberg₂ z Φ hΦ
  · intro h
    obtain ⟨b, hb⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
    obtain ⟨f, rfl⟩ := hsurj b
    exact hb (by rw [h]; rfl)
  · intro v
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
    · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), hSB v]
  · intro f φ hφ hφv
    funext y
    rw [LinearMap.smul_apply, hpure f φ hφ hφv]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, LinearMap.smul_apply]
    have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
      refine hfin0.subset fun v hv h => hv ?_
      simp [h]
    have hfin2 := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n × Fin d) (fun v => ev v (φ v)) (by
      filter_upwards [hφv, hstd] with v h1 h2
      rw [h1, h2]) y
    rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
    ring
  · rw [← hl1 x hx, hxy, hl1 y hy]

theorem evBij_of_adel (hA : PositivityTheory.Mix.AdelSt) : EvBij := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ hM' =>
  isEv_bij_of_adel hA hP.base hP.herm hP.skew hP.good hM'

theorem evCone_of_adel (hA : PositivityTheory.Mix.AdelSt) : EvCone := evCone_of_bij (evBij_of_adel hA)

theorem evZero_of_adel (hA : PositivityTheory.Mix.AdelSt) (hDq : SchwartzDq) (h : AdaptedModelEvaluationAtZero) : EvZero := evZero_of_bij (evBij_of_adel hA) hDq h

end PositivityTheory.ThKF0
end
end
end
