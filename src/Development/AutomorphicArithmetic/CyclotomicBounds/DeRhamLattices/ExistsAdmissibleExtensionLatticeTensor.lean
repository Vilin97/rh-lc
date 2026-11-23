module

public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleLatticeMatrixOfPeriodData
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActExtLApply

section

@[expose] public section



open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

variable {L X χ₁ z}

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
end
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmulSurjectiveRankOne

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one :
    ∀ {O T X : Type} [inst : CommRing O]
    [inst_1 : AddCommGroup T] [inst_2 : _root_.Module O T] [inst_3 : AddCommGroup X] [inst_4 : _root_.Module O X]
    (x₀ : X), (∀ (x : X), ∃ (c : O), x = c • x₀) → ∀ (m : TensorProduct O T X), ∃ (t : T), t ⊗ₜ[O] x₀ = m := by
  intro O T X _ _ _ _ _ x₀ h m
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.zero_tmul T x₀⟩
  | tmul t x =>
    obtain ⟨c, rfl⟩ := h x
    exact ⟨c • t, TensorProduct.smul_tmul c t x₀⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, TensorProduct.add_tmul s t x₀⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleExtensionLatticeTensor

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem twisted_matrix_mulVec_base_change {G O LL : Type} [Group G] [CommRing O] [Field LL] [Algebra O LL] {n : ℕ}
    (M : G →* Matrix (Fin n) (Fin n) O) (θ : G →* Oˣ) (g : G) (v : Fin n → LL) :
    ((twistM M θ g).map (algebraMap O LL)).mulVec v = ((θ g : Oˣ) : O) • ((M g).map (algebraMap O LL)).mulVec v := by
  have : (twistM M θ g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (M g).map (algebraMap O LL) := by
    ext i j
    change algebraMap O LL (((θ g : Oˣ) : O) * M g i j) = ((θ g : Oˣ) : O) • algebraMap O LL (M g i j)
    rw [map_mul, Algebra.smul_def]
  rw [this, Matrix.smul_mulVec]

private theorem mulVec_smul_scalar {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) LL) (s : O) (v : Fin n → LL) : M.mulVec (s • v) = s • M.mulVec v := by
  rw [Matrix.mulVec_smul]

private theorem tmul_surjective_rank_one {O T X : Type} [CommRing O] [AddCommGroup T] [Module O T] [AddCommGroup X] [Module O X]
    (x₀ : X) (h : ∀ x : X, ∃ c : O, x = c • x₀) (m : T ⊗[O] X) : ∃ t : T, t ⊗ₜ[O] x₀ = m :=
  _root_.UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one x₀ h m

theorem _root_.UpperTheory.KN.exists_admissible_extension_latticeTensor :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ : G →* Oˣ) (p : Xs)
      {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
      (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (z : G → ↥L.T ⊗[O] X)
      (iW : V →ₗ[LL] (Fin n → LL)) (e : Fin n → LL) (x₀ : X),
      χ = θ → lam ≠ 0 → (∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ)))) →
      HasPres LL N (fun g => tableLineDegreeTwo.actTw L X χ g) z →
      Function.Injective iW → (∀ g v, iW (ρ g v) = ((θ g : Oˣ) : O) • ((N p g).map (algebraMap O LL)).mulVec (iW v)) →
      e ≠ 0 → (∀ g, ((N p g).map (algebraMap O LL)).mulVec e = e) → (∀ x : X, ∃ c : O, x = c • x₀) →
      ∀ b : ℕ, (∀ x : X, lam ^ b • x = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT (tableLineDegreeTwo.actExt L X χ z) (tableLineDegreeTwo.kerExt L X lam b) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    Xs n N θ χ p V _ _ _ _ ρ L X _ _ z iW e x₀ hχ hlam hfull hpres hiW hρ he hfix hx₀ b hb
  subst hχ
  obtain ⟨a, x, E, Y, hfg, hst, hE, φ, hφ, hz⟩ := hpres
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
  haveI : Module.IsTorsionFree O (Fin n → LL) := Module.IsTorsionFree.trans_faithfulSMul O LL _
  let j : (↥Y × ↥L.T × O) →ₗ[O] ((Fin a ⊕ Bool) → Fin n → LL) :=
    { toFun := fun u => Sum.elim (fun k => (u.1 : Fin a → Fin n → LL) k + u.2.2 • E k)
        (fun c => cond c (iW (u.2.1 : V)) (u.2.2 • e))
      map_add' := by
        intro u v
        funext k
        rcases k with k | _ | _
        · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, add_smul]
          abel
        · simp [add_smul]
        · simp
      map_smul' := by
        intro c u
        funext k
        rcases k with k | _ | _
        · simp [mul_smul, smul_add]
        · simp [mul_smul]
        · simp }
  let actA : G → (↥Y × ↥L.T × O) → (↥Y × ↥L.T × O) := fun g u =>
    (((χ g : Oˣ) : O) • (⟨_, hst g u.1.1 u.1.2⟩ : ↥Y) + (u.2.2 * ((χ g : Oˣ) : O)) • (⟨_, hE g⟩ : ↥Y),
      actT L g u.2.1, ((χ g : Oˣ) : O) * u.2.2)
  let q0 : (↥Y × ↥L.T × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
    LinearMap.prod (φ ∘ₗ LinearMap.fst O _ _ +
        (TensorProduct.mk O ↥L.T X).flip x₀ ∘ₗ LinearMap.fst O _ _ ∘ₗ LinearMap.snd O _ _)
      (LinearMap.snd O _ _ ∘ₗ LinearMap.snd O _ _)
  have hq0 : ∀ u, q0 u = (φ u.1 + u.2.1 ⊗ₜ[O] x₀, u.2.2) := fun u => rfl
  have hq0a : ∀ g u, q0 (actA g u) = tableLineDegreeTwo.actExt L X χ z g (q0 u) := by
    intro g u
    rw [hq0, hq0]
    simp only [actA, tableLineDegreeTwo.actExt, map_add (f := _), map_smul, hφ, ← hz, tableLineDegreeTwo.actTw, LinearMap.smul_apply, smul_smul,
      Units.mul_inv, one_smul, LinearMap.rTensor_tmul]
    refine Prod.ext ?_ rfl
    simp only
    abel
  refine UpperTheory.KN.exists_admissible_lattice_matrix_of_period_data PD emb lam jT cT (fun k : Fin a ⊕ Bool => twistM (N (Sum.elim x (fun _ => p) k)) χ)
    j actA _ _ ((tableLineDegreeTwo.kerExt L X lam b).mkQ ∘ₗ q0) (lam ^ b) (fun k => hfull _) ?_ ?_ ?_ ?_ (pow_ne_zero _ hlam)
    (GlobalTheory.UseLoc.Cases.AdmW.kerExt_kill L X lam b hb)
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, t, s⟩ h
    have h1 : s • e = 0 := congrFun h (Sum.inr false)
    have h2 : iW (t : V) = 0 := congrFun h (Sum.inr true)
    have hs : s = 0 := (smul_eq_zero.mp h1).resolve_right he
    have ht : t = 0 := Subtype.ext (hiW (h2.trans (map_zero iW).symm))
    have hy : y = 0 := by
      apply Subtype.ext
      funext k
      have h3 : (y : Fin a → Fin n → LL) k + s • E k = 0 := congrFun h (Sum.inl k)
      rw [hs, zero_smul, add_zero] at h3
      exact h3
    rw [hs, ht, hy]
    rfl
  · rintro g ⟨y, t, s⟩
    funext k
    unfold actN
    rw [twisted_matrix_mulVec_base_change]
    rcases k with k | _ | _
    · change ((χ g : Oˣ) : O) • ((N (x k) g).map (algebraMap O LL)).mulVec ((y : Fin a → Fin n → LL) k) +
          (s * ((χ g : Oˣ) : O)) • (((N (x k) g).map (algebraMap O LL)).mulVec (E k) - E k) +
          (((χ g : Oˣ) : O) * s) • E k =
        ((χ g : Oˣ) : O) • ((N (x k) g).map (algebraMap O LL)).mulVec ((y : Fin a → Fin n → LL) k + s • E k)
      rw [Matrix.mulVec_add, mulVec_smul_scalar, smul_add, smul_smul, mul_comm s, smul_sub]
      abel
    · change (((χ g : Oˣ) : O) * s) • e = ((χ g : Oˣ) : O) • ((N p g).map (algebraMap O LL)).mulVec (s • e)
      rw [mulVec_smul_scalar, hfix, smul_smul]
    · exact hρ g (t : V)
  · refine (Submodule.mkQ_surjective _).comp ?_
    rintro ⟨m, s⟩
    obtain ⟨t, rfl⟩ := tmul_surjective_rank_one x₀ hx₀ m
    exact ⟨(0, t, s), by rw [hq0]; simp⟩
  · intro g u w hw
    have hw' : q0 u - w ∈ tableLineDegreeTwo.kerExt L X lam b := (Submodule.Quotient.eq _).mp hw
    have h := GlobalTheory.UseLoc.Cases.AdmW.actExtL_ker L X χ z lam b hb g hw'
    rw [Submodule.mem_comap, map_sub, GlobalTheory.UseLoc.Cases.AdmW.actExtL_apply,
      GlobalTheory.UseLoc.Cases.AdmW.actExtL_apply, ← hq0a] at h
    exact (Submodule.Quotient.eq _).mpr h
end
end
