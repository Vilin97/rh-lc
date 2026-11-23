module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVRStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  first | exact @GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | exact GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | (intros; apply GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTriple

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TripleTrace

open GlobalTheory.BlockComplement

theorem continuous_twO (D : D7) (a : D.nd.Loc) : Continuous (D.ntw.twist₂ a) := by
  have hl := GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)
  have hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0 := by
    intro h0
    have := congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0
    rw [map_natCast, map_zero] at this
    exact (D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)
  have hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime := Ideal.comap_isPrime _ _
  have hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal := hp.isMaximal fun h => by
    apply hl0
    rw [← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]
    exact hl
  have he := IsLocalRing.eq_maximalIdeal hm
  refine continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_
  rw [ContinuousAt, map_zero,
    (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  rw [← he] at hx
  exact Ideal.le_comap_pow _ n hx

theorem trace_of_block {K : Type} [Field K] {n a t : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (M' : Matrix (Fin a) (Fin a) K) (c : Fin t → K) (e : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin t → K)))
    (h : ∀ u, e (M.mulVec u) = (M'.mulVec (e u).1, fun j => c j * (e u).2 j)) :
    M.trace = M'.trace + ∑ j, c j := by
  have e1 : e.conj (Matrix.toLin' M) =
      LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]
    refine Prod.ext rfl ?_
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap',
    Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]

theorem trace_eq : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  rintro hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g
  have hι := GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i
  have hinj : Function.Injective (iotaOQ D.nd D.naut i) :=
    (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  apply hinj
  revert g
  rw [← funext_iff]
  refine AE.eq_of_continuous hC (hι.comp hρ.matrix_trace)
    (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_
  filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i,
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv),
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)]
    with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ
  apply (D.naut.iotaQC i).injective
  have hq := normV_ne_zero w
  have h6 := D.naut.pt_loc i P π hP w (h4 hw)
  rw [← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw] at h6
  have h9 := map_trace_eq_sum _ _ _ h6
  have h10 := map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)
  rw [D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2] at h9
  rw [D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2] at h10
  have h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) =
      sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w *
        ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) := by
    rw [sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast,
      mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  have h11 := congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))
  have h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace =
      iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace +
        ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) := by

    simp only [map_add (f := _), map_sum] at h11
    refine Eq.trans ?_ (h11.trans ?_)
    · exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)
    · congr 1
      exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm
  refine Eq.trans ?_ h10.symm
  have h13 := h12.symm.trans h9
  rw [h7] at h13
  simp only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, add_mul] at h13
  exact add_right_cancel h13

end GlobalTheory.TripleTrace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTripleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

theorem _root_.GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  first | exact @GlobalTheory.TripleTrace.trace_eq | exact GlobalTheory.TripleTrace.trace_eq | (intros; apply GlobalTheory.TripleTrace.trace_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRhoConjLatTpsi

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem twist_conj {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin k) B) (ρ₀ : Γ →* GL (Fin k) A) (χ₀ : Γ →* Aˣ) (ψ χ : Γ →* Bˣ)
    (hχ : χ = (Units.map (f : A →* B)).comp χ₀ * ψ) (U : GL (Fin k) B)
    (hU : ∀ g, mapRep f ρ₀ g * U = U * ρ g) (g : Γ) :
    twistM ((Units.coeHom _).comp ρ) χ⁻¹ g * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        twistM (mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹)) ψ⁻¹ g := by
  have h1 : ρ g * U⁻¹ = U⁻¹ * mapRep f ρ₀ g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hU, mul_inv_cancel_right]
  have h2 : ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := congrArg Units.val h1
  have h3 : mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g =
      f (((χ₀ g)⁻¹ : Aˣ) : A) • ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := by
    ext i j
    exact map_mul f _ _
  have h4 : (((χ g)⁻¹ : Bˣ) : B) = (((ψ g)⁻¹ : Bˣ) : B) * f (((χ₀ g)⁻¹ : Aˣ) : A) := by
    rw [hχ, MonoidHom.mul_apply, mul_inv_rev, Units.val_mul, MonoidHom.comp_apply, ← map_inv]
    rfl
  change ((((χ g)⁻¹ : Bˣ) : B) • ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)) * _ =
    _ * ((((ψ g)⁻¹ : Bˣ) : B) • mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g)
  rw [h3, smul_smul, ← h4, Matrix.smul_mul, Matrix.mul_smul, h2]

theorem twistedRho_conj_latTpsi : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π) → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → AbsIrrSub (redRep D.nd a (ρ π)) ⊤ → ∃ U : GL (Fin D.R.r) (D.nd.O a), ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) = (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g := by
  intro hC D a π ρ s Sg hρ hP hT hirr
  have htr := GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple hC D a π (ρ π) s Sg hρ hP hT
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR (D.nd.O a) (Formalism.MainNotions.N.GE D.nd) D.R.r (ρ π)
    (mapRep (D.ntw.twist₂ a) (D.ntw.rhoS _ s)) hirr (fun g => by
      rw [htr g]
      exact (AddMonoidHom.map_trace (D.ntw.twist₂ a) _))
  refine ⟨U⁻¹, fun g => ?_⟩
  refine twist_conj (D.ntw.twist₂ a) (ρ π) (D.ntw.rhoS _ s) _ (D.ntw.psiL a) (D.nd.chi a 1) ?_ U hU g
  rw [hT.1, hT.2.1]
  exact D.ntw.chi_tw a

end GlobalTheory.PtCore
end
end
