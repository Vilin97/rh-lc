module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLatticeStatement
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBlochKatoLatticeDualOrthogonalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientFieldStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModulesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.local_duality_finite_discrete_modules : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.DualPairFormula.greenbergWiles_dualPair | exact GlobalTheory.DualPairFormula.greenbergWiles_dualPair | (intros; apply GlobalTheory.DualPairFormula.greenbergWiles_dualPair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidual

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual.Perp

theorem ker_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x : O) :
    algebraMap O K x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O := by
  refine ⟨fun hx => ?_, h x⟩
  by_contra hn
  have hu : IsUnit x := by simpa using hn
  exact (hu.map (algebraMap O K)).ne_zero hx

theorem eq_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ algebraMap O K x = algebraMap O K y := by
  rw [← ker_iff h, map_sub, sub_eq_zero]

def divMap {O : Type} [CommRing O] [IsDomain O] (ϖ : O) : O →ₗ[O] Formalism.BasicNotions.KmodO O :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹) ∘ₗ Algebra.linearMap O (FractionRing O)

theorem divMap_apply {O : Type} [CommRing O] [IsDomain O] (ϖ a : O) :
    divMap ϖ a = Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem divMap_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : divMap ϖ a = 0 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  rw [divMap_apply, Submodule.Quotient.mk_eq_zero, map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨b, rfl⟩

theorem continuous_algebraMap {O K : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Field K] [Algebra O K] [TopologicalSpace K]
    (ha : IsAdic (IsLocalRing.maximalIdeal O))
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) : Continuous (algebraMap O K) := by
  have ho : IsOpen (IsLocalRing.maximalIdeal O : Set O) := by simpa using (isAdic_iff.1 ha).1 1
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (IsLocalRing.maximalIdeal O : Set O), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  exact (eq_iff h y x).1 hy

theorem repOn_one_map {G O K : Type} [Group G] [CommRing O] [Field K] [Algebra O K] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (g : G) (y : Fin r → O) (a : Fin r) :
    repOn ρ (1 : G →* Kˣ) K g (fun b => algebraMap O K (y b)) a =
      algebraMap O K (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).mulVec y a) := by
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem mem_bkOn_of_orthogonal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  intro D N X bkP i s hG K _ _ _ _ hK hs ρ hρ v hv y H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  choose lift hlift using hs
  have hy : ∀ g, y.1 g = fun b => algebraMap (X.O0 i) K (lift (y.1 g b)) := fun g => funext fun b => (hlift _).symm
  have hact : ∀ (g h : DecV N v) a, ((red i K ρ).comp (DecV N v).subtype) g (y.1 h) a =
      algebraMap (X.O0 i) K ((Tdual i s g.1).mulVec (fun b => lift (y.1 h b)) a) := fun g h a => by
    rw [← hρ g.1, ← repOn_one_map ρ g.1, ← hy]
    rfl
  have key := (GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice D N X bkP i s hG ρ hρ v hv ϖ hϖ (fun g a => lift (y.1 g a)) (fun a => ?_)
    (fun g h a => ?_)).2 ?_
  · obtain ⟨y', hy', e⟩ := key
    obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hy'
    unfold bkOn
    rw [dite_eq_left hv]
    refine Submodule.subset_span ⟨y, c, y', 1, hc, hc', fun g a => ?_, rfl⟩
    rw [smul_eq_mul, mul_one, (eq_iff hK _ _).1 (e g a), hlift]
  · have : IsLocallyConstant fun g => y.1 g a :=
      (IsLocallyConstant.iff_continuous _).2 ((continuous_apply a).comp y.2.1)
    exact this.comp fun k => IsLocalRing.residue (X.O0 i) (lift k)
  · rw [eq_iff hK, map_add (f := _), hlift, hlift, ← hact, y.2.2 g h]
    rfl
  · intro d hd
    let x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype) :=
      ⟨fun g a => algebraMap (X.O0 i) K (d g a),
        continuous_pi fun a => (continuous_algebraMap (X.twistBaseCoefficientRing_isAdic i) hK).comp ((continuous_apply a).comp hd.continuous),
        fun g h => funext fun a => by
          beta_reduce
          rw [hd.cocycle g h, Pi.add_apply, map_add (f := _), ← repOn_one_map]
          rfl⟩
    have hx : Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v := by
      obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hd
      unfold bkOn
      rw [dite_eq_left hv]
      exact Submodule.subset_span ⟨x, c, d, 1, hc, hc', fun g a => by rw [smul_eq_mul, mul_one], rfl⟩
    obtain ⟨f, hf, e⟩ := H x hx
    refine ⟨fun g => divMap ϖ (lift (f g)), hf.comp fun k => divMap ϖ (lift k), fun g h => ?_⟩
    rw [← divMap_apply, ← map_smul, ← map_sub, ← map_add (f := _), ← sub_eq_zero, ← map_sub]
    apply divMap_eq_zero hϖ
    rw [eq_iff hK, map_add (f := _), map_sub, smul_eq_mul, map_mul, hlift, hlift, hlift, ← e g h]

    simp only [dotProductBilin_apply_apply, dotProduct, map_sum, map_mul, hact]
    rfl

end GlobalTheory.ResDual.Perp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidualStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.mem_dualBlochKato_of_orthogonal_residual : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  first | exact @GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | exact GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | (intros; apply GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDual

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual

theorem eq_zero_of_forall_eigen {k : Type} [Field k] {r : ℕ} (hr : 2 ≤ r) (m : Fin r → k)
    (h : ∀ A : Matrix (Fin r) (Fin r) k, A.mulVec m ∈ Submodule.span k {m}) : m = 0 := by
  by_contra hm
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hm
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h (Matrix.single b a 1))
  have h1 := congrFun hc a
  have h2 := congrFun hc b
  simp [Matrix.single_mulVec, Function.update, hb.symm] at h1 h2
  rcases h1 with rfl | h1
  · exact ha (by simpa using h2.symm)
  · exact ha h1

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem red_apply (i : X.Tw) (K : Type) [Field K] [Algebra (X.O0 i) K] (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N)
    (m : Fin D.R.r → K) :
    red i K ρ g m = (((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equiv {i : X.Tw} {s : X.Sig i} (K : Type) [Field K] [Algebra (X.O0 i) K] {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)}
    (hρ : IsDual i s ρ) (g : GE N) (x y : Fin D.R.r → K) :
    dotProductBilin K K (red i K (Tgl i s) g x) (red i K ρ g y) =
      algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * dotProductBilin K K x y := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [red_apply, red_apply, hρ, Tgl_coe, Tdual, dotProductBilin_apply_apply, dotProductBilin_apply_apply,
    Matrix.map_smul' _ _ _ (map_mul _), Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.transpose_map,
    Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
    Matrix.nonsing_inv_mul _ h3, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, dotProduct_comm]

theorem Tmat_map_residue (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) =
      IsLocalRing.residue (X.O0 i) (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • rbar X i s g := by
  rw [Tmat, Matrix.map_smul' _ _ _ (map_mul _)]
  rfl

theorem residue_unit_ne_zero {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) : IsLocalRing.residue O (u : O) ≠ 0 :=
  (u.isUnit.map _).ne_zero

section NoInv

variable {i : X.Tw} {s : X.Sig i} (hr : 2 ≤ D.R.r)
  (hs : Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤)
include hr hs

theorem h0_red : H0 (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  refine eq_zero_of_forall_eigen hr m fun A => ?_
  have hA : A ∈ Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) := hs ▸ Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    have e := hm g
    rw [red_apply, Tgl_coe, IsLocalRing.ResidueField.algebraMap_eq, Tmat_map_residue, Matrix.smul_mulVec] at e
    rw [← Submodule.smul_mem_iff _ (residue_unit_ne_zero (chiS i s g)⁻¹), e]
    exact Submodule.mem_span_singleton_self m
  | zero => simp
  | add A B _ _ hA hB => rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ c hA

theorem h0_red_dual {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) :
    H0 (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  refine eq_zero_of_forall_eigen hr m fun A => ?_
  rw [← A.transpose_transpose]
  have hA : A.transpose ∈ Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) :=
    hs ▸ Submodule.mem_top
  generalize A.transpose = B at hA
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    have e := hm g⁻¹
    rw [red_apply, hρ, Tdual, GlobalTheory.PrimeToInertia.Tmat_inv, inv_inv, Matrix.map_smul' _ _ _ (map_mul _),
      Matrix.transpose_map, IsLocalRing.ResidueField.algebraMap_eq, Tmat_map_residue, Matrix.transpose_smul,
      Matrix.smul_mulVec, Matrix.smul_mulVec] at e
    rw [← Submodule.smul_mem_iff _ (residue_unit_ne_zero (chiS i s g)⁻¹),
      ← Submodule.smul_mem_iff _ (residue_unit_ne_zero (eps0 X i g⁻¹)), e]
    exact Submodule.mem_span_singleton_self m
  | zero => simp
  | add A B _ _ hA hB => rw [Matrix.transpose_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => rw [Matrix.transpose_smul, Matrix.smul_mulVec]; exact Submodule.smul_mem _ c hA

end NoInv

theorem cupCob_of_mk_eq_zero {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M']
    (χ : Γ → k) (ρ : Representation k Γ M) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (x : Z1 ρ) (y : Z1 ρ')
    (hx : (Submodule.Quotient.mk x : H1 ρ) = 0) : CupCob χ ρ' P x.1 y.1 := by
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ x.1).1 hx
  refine ⟨fun g => P m (y.1 g), ((IsLocallyConstant.iff_continuous _).2 y.2.1).comp (P m), fun g h => ?_⟩
  have e : x.1 g = ρ g m - m := hm g
  simp only [e, y.2.2 g h, map_sub, map_add (f := _), LinearMap.sub_apply, hP]
  ring

theorem residue_globalCyclotomicCharacter (i : X.Tw) (g : GE N) :
    algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i)) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
      (((cycMod D.host.E N.Om (X.l i) 1 g : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)).val :
        IsLocalRing.ResidueField (X.O0 i)) := by
  set z : ℤ_[X.l i] := ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])
  change IsLocalRing.residue _ (algebraMap ℤ_[X.l i] (X.O0 i) z) = ((PadicInt.toZModPow 1 z).val : _)
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have h : z - ((PadicInt.toZModPow 1 z).val : ℕ) ∈ RingHom.ker (PadicInt.toZModPow (p := X.l i) 1) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  have h0 : IsLocalRing.residue (X.O0 i) (X.l i : X.O0 i) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 (GlobalTheory.PrimeToInertia.l_mem i)
  have := congrArg (fun t => IsLocalRing.residue _ (algebraMap ℤ_[X.l i] (X.O0 i) t)) hw
  simp only [map_sub, map_mul, map_natCast, pow_one] at this
  rw [map_natCast] at h0
  rw [h0, zero_mul, sub_eq_zero] at this
  exact this

theorem Tmat_eq_one {bkP : BKPh X} {i : X.Tw} {s : X.Sig i} (h : GalHyp bkP i s) {v : PlE D.host}
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl (X := X) i) (B : ValuationSubring N.Om) (hB : IsPlaceOver B v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) B) : Tmat i s σ = 1 := by
  have h1 : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have h2 : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  rw [Tmat, h.1.1 v hl h1 B hB σ hσ, chiS, X.twistCharacterFamily_unramified i _ _ v hl h1 h2 B hB σ hσ]
  simp

theorem nrComplexPlaces_host (D : Formalism.BasicNotions.D7) [_root_.NumberField.IsTotallyComplex D.host.E] :
    InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
  have h1 := IsTotallyComplex.finrank D.host.E
  have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  omega



theorem card_eq (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality) (hLE : LocalEulerChar)
    (hGF : GlobalFiniteness) (hGE : GlobalEulerChar) (h4 : Gen.ArchimedeanSignatureMatching) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i)
    (h : GalHyp bkP i s) [TopologicalSpace (IsLocalRing.ResidueField (X.O0 i))]
    [DiscreteTopology (IsLocalRing.ResidueField (X.O0 i))] (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (hρ : IsDual i s ρ) :
    Finite (selOn bkP i (Tgl i s) (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) ∧
    Finite (selOn bkP i ρ (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) ∧
    Nat.card (selOn bkP i (Tgl i s) (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ)
      (IsLocalRing.ResidueField (X.O0 i)) ∅) =
    Nat.card (selOn bkP i ρ (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) := by
  classical
  have hl : (X.l i).Prime := Fact.out
  have : Finite (IsLocalRing.ResidueField (X.O0 i)) := X.twistBaseCoefficientRing_residueField_finite i
  have : CharP (IsLocalRing.ResidueField (X.O0 i)) (X.l i) := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (IsLocalRing.residue (X.O0 i)), IsLocalRing.residue_eq_zero_iff]
    exact GlobalTheory.PrimeToInertia.l_mem i)
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hres : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx => (IsLocalRing.residue_eq_zero_iff _).2 hx
  have hsurj : Function.Surjective (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) := IsLocalRing.residue_surjective
  have hloc : IsLocalHom (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) := inferInstanceAs (IsLocalHom (IsLocalRing.residue (X.O0 i)))
  have hr : 2 ≤ D.R.r := le_trans (by norm_num) h.2.2.2.2.2.2
  have htors : ∀ b : (IsLocalRing.ResidueField (X.O0 i)), ∃ n, ∀ x ∈ IsLocalRing.maximalIdeal (IsLocalRing.ResidueField (X.O0 i)) ^ n, x • b = 0 := fun b => ⟨1, fun x hx => by
    rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
    rw [hx, zero_smul]⟩
  have hker : IsOpen (((1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ).ker : Subgroup (GE N)) : Set (GE N)) := by
    rw [MonoidHom.ker_one]; exact isOpen_univ
  have hc : ContAction (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) := GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _
    (by simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s) _ hker htors
  have hc' : ContAction (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) := GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _
    (by simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s) _ hker htors
  let Sl : Finset (PlE D.host) := (X.S0 i).filter (· ∈ placesOver D.host.E (X.l i))
  let Sp : Finset (PlE D.host) := (X.S0 i).filter (· ∈ Spl (X := X) i)
  have hSl : ∀ v, v ∈ Sl ↔ v ∈ placesOver D.host.E (X.l i) := fun v =>
    ⟨fun hv => (Finset.mem_filter.1 hv).2, fun hv => Finset.mem_filter.2 ⟨X.twistExcludedPlaces_contains_residueChar i hv, hv⟩⟩
  have hSp : ∀ v, v ∈ Sp ↔ v ∈ Spl (X := X) i := fun v =>
    ⟨fun hv => (Finset.mem_filter.1 hv).2, fun hv => Finset.mem_filter.2 ⟨by
      rcases hv.1 with h1 | h1
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h1
        exact X.placesOver_subset_exceptional i j hj
      · exact X.primes_subset_exceptional i h1, hv⟩⟩
  have hdis : Disjoint Sl Sp := Finset.disjoint_left.2 fun v h1 h2 => ((hSp v).1 h2).2 ((hSl v).1 h1)
  have hnot : ∀ v ∉ Sl ∪ Sp, v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i := fun v hv => by
    rw [Finset.mem_union, not_or, hSl, hSp] at hv
    exact hv
  have van := fun v (hv : v ∈ Spl (X := X) i) => GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s h v hv (IsLocalRing.ResidueField (X.O0 i)) 1 hker
    (fun g => ⟨0, by simp⟩) (IsLocalRing.ResidueField (X.O0 i)) htors (Tgl i s) (Or.inl rfl)
  have cl : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∈ placesOver D.host.E (X.l i) →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v =
        bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i)) v := fun τ v hv => if_pos hv
  have cp : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∈ Spl (X := X) i →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v = ⊤ :=
    fun τ v hv => (if_neg hv.2).trans (if_pos (Or.inl hv))
  have cu : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∉ Sl ∪ Sp →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v =
        Formalism.GaloisCohomology.unrAt (red i (IsLocalRing.ResidueField (X.O0 i)) τ) (N.plOm.1 v) :=
    fun τ v hv => (if_neg (hnot v hv).1).trans (if_neg (by simpa using (hnot v hv).2))
  obtain ⟨f1, f2, e⟩ := GlobalTheory.T.local_duality_finite_discrete_modules hPT hLF hGF hGE D.host.E N.Om (X.l i) (IsLocalRing.ResidueField (X.O0 i)) (Fin D.R.r → (IsLocalRing.ResidueField (X.O0 i))) (Fin D.R.r → (IsLocalRing.ResidueField (X.O0 i)))
    (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) (fun g => algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i)) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i))
    (dotProductBilin (IsLocalRing.ResidueField (X.O0 i)) (IsLocalRing.ResidueField (X.O0 i))) hc hc' (residue_globalCyclotomicCharacter i)
    (fun x hx => funext fun a => by simpa using hx (Pi.single a 1))
    (fun y hy => funext fun a => by simpa using hy (Pi.single a 1))
    (dot_equiv (IsLocalRing.ResidueField (X.O0 i)) hρ) (Sl ∪ Sp) N.plOm (fun v hv => Finset.mem_union_left _ ((hSl v).2 hv))
    (fun v hv B hB σ hσ => LinearMap.ext fun m => by
      rw [red_apply, Tgl_coe, Tmat_eq_one h (hnot v hv).1 (hnot v hv).2 B hB σ hσ,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Module.End.one_apply])
    _ _ (cu (Tgl i s)) (cu ρ) (fun v hv y => by
      rcases Finset.mem_union.1 hv with hv | hv
      · rw [hSl] at hv
        rw [cl _ v hv, cl _ v hv]
        exact ⟨fun hy x hx => GlobalTheory.T.residualBlochKato_lattice_dual_orthogonal hLD D N X bkP i s h (IsLocalRing.ResidueField (X.O0 i)) hres ρ hρ v hv x y hx hy,
          GlobalTheory.T.mem_dualBlochKato_of_orthogonal_residual D N X bkP i s h (IsLocalRing.ResidueField (X.O0 i)) hres hsurj ρ hρ v hv y⟩
      · rw [hSp] at hv
        rw [cp _ v hv, cp _ v hv]
        refine ⟨fun _ x _ => cupCob_of_mk_eq_zero _ _ _ _ (fun g => dot_equiv (IsLocalRing.ResidueField (X.O0 i)) hρ g.1) x y ?_, fun _ => Submodule.mem_top⟩
        exact (van v hv).2.1.elim _ _)
  refine ⟨f1, f2, ?_⟩
  have hset : Setup bkP i s (1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ) ∅ :=
    ⟨h, hloc, Module.Finite.of_surjective (Algebra.linearMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) hsurj, hker, fun g => ⟨0, by simp⟩,
      fun _ _ _ _ _ _ => rfl, by simp, fun _ _ _ _ _ _ => rfl⟩
  have cnt := GlobalTheory.T.local_count_of_setup hLF hLD hLE h4 D N X bkP i s (IsLocalRing.ResidueField (X.O0 i)) 1 ∅ hset (IsLocalRing.ResidueField (X.O0 i)) inferInstance
  have hSl' : placesOver D.host.E (X.l i) = (Sl : Set (PlE D.host)) := Set.ext fun v => (hSl v).symm
  rw [hSl', finprod_mem_coe_finset, finprod_mem_coe_finset] at cnt
  rw [Finset.prod_union hdis, Finset.prod_union hdis, h0_red hr h.2.1.1, h0_red_dual hr h.2.1.1 hρ,
    Finset.prod_eq_one (s := Sp) (fun v hv => by rw [(van v ((hSp v).1 hv)).1]; simp),
    Finset.prod_eq_one (s := Sp) (fun v hv => by
      have := (van v ((hSp v).1 hv)).2.1
      exact Nat.card_unique),
    Finset.prod_congr rfl (fun v hv => congrArg (fun L : Submodule (IsLocalRing.ResidueField (X.O0 i)) _ => Nat.card L) (cl (Tgl i s) v ((hSl v).1 hv))),
    cnt, nrComplexPlaces_host, Nat.card_fun, Nat.card_fin, ← pow_mul, mul_comm D.R.r] at e
  have hpos : 0 < (∏ v ∈ Sl, Nat.card (H0 ((repOn (Tgl i s) (1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ) (IsLocalRing.ResidueField (X.O0 i))).comp (DecV N v).subtype))) *
      Nat.card (IsLocalRing.ResidueField (X.O0 i)) ^ (D.R.f * D.R.r) :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  simp only [Nat.card_unique, mul_one] at e
  rw [← mul_assoc]
  exact e

theorem finrank_eq_of_card_eq {k V V' : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] (f : Finite V) (f' : Finite V') (e : Nat.card V = Nat.card V') :
    Module.finrank k V = Module.finrank k V' := by
  rw [Module.natCard_eq_pow_finrank (K := k), Module.natCard_eq_pow_finrank (K := k) (V := V')] at e
  exact Nat.pow_right_injective Finite.one_lt_card e

theorem eqDim : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → EqDim bkP i s := by
  intro _ hPT _ _ hLF hLD hLE hGF hGE _ h4 D N X bkP i s h K _ _ _ _ hK ρ hρ
  letI : TopologicalSpace (IsLocalRing.ResidueField (X.O0 i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (X.O0 i)) := ⟨rfl⟩
  obtain ⟨f1, f2, e⟩ := card_eq hPT hLF hLD hLE hGF hGE h4 bkP i s h ρ hρ
  have := X.twistBaseCoefficientRing_residueField_finite i
  have hres : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx => (IsLocalRing.residue_eq_zero_iff _).2 hx
  have hsurj : Function.Surjective (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) :=
    IsLocalRing.residue_surjective
  obtain ⟨a1, a2⟩ := GlobalTheory.T.residualSelmer_baseChange_coefficientField D N X bkP i (Tgl i s) _ K hres hsurj hK ∅ Module.Finite.of_finite
  obtain ⟨b1, b2⟩ := GlobalTheory.T.residualSelmer_baseChange_coefficientField D N X bkP i ρ _ K hres hsurj hK ∅ Module.Finite.of_finite
  refine ⟨a1, b1, ?_⟩
  rw [a2, b2]
  exact finrank_eq_of_card_eq f1 f2 e

end GlobalTheory.ResDual
end
end
end
