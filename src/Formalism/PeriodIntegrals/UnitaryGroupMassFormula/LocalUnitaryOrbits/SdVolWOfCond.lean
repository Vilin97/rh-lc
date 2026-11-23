module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
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
import Mathlib.RingTheory.TotallySplit
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRSmulF
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermSmulRight

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdxPiWStd

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem latIdx (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem lamIdx (a : ℕ) (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a) := by
  have hV := latIdx v Λ b hb hmem hR ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem basis_of (hCM : IsCMExt F E σ) (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      ∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem smul_tup {a : ℕ} (ϖ : Fv F v) (p : TupV (E := E) v n a) : ϖ • p = sc (E := E) v ϖ • p := by
  funext i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem idxPiW_std (a : ℕ) (hS : StdHyp σ J ψ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : IdxPiW v Λ a := by
  obtain ⟨L, hLat, rfl⟩ := hFull
  rintro _ _ ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := basis_of σ v hS.1 L hLat
  have e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ := by
    ext X
    rw [mem_smulSub, lamP, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
  have e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a := AddSubgroup.ext fun _ => Iff.rfl
  rw [e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]
  push_cast
  ring

end PI.OmLocU.SdB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntSmulMemAll

section

@[expose] public section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isOpen_latLoc <;> assumption

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isCompact_latLoc <;> assumption

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hFull⟩

end TopWs

end PI.OmLocU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPi

section

@[expose] public section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sdVolW_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of_top σ J ψ v Λ a hC (topW_holds v Λ a hFull) hD hI

theorem sdVolH_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxHO σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of_top σ J ψ v a hC (topH_holds v σ a) hD hI

theorem sdVolW_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxPiW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of σ J ψ v Λ a hC hD (idxW_of v Λ a hI) hFull

theorem sdVolH_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxPiH σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of σ J ψ v a hC hD (idxHO_of σ v a hI)

end PI.OmLocU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfCond

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

def CondAllF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem condV_of_all (h : CondAllF) : CondV σ J ψ v := by
  intro hs t
  rw [← h F hs.1.1 ψ hs.2.2.1 hs.2.2.2 v t]
  exact forall₂_congr fun s _ => by rw [mul_comm]

attribute [local instance] LocMassOrdSF.isModTop_tens in
private theorem fullLattice_of_isSDLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hSD : IsSDLoc σ J v (L : Set (Fin n → E))) :
    Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hL, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro x _
  by_contra hx
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem hx
  let A := Fv F v ⊗[F] E
  let ι : E →+* A := inclR (F := F) (Fv F v)
  let f : (Fin n → A) →ₗ[A] A :=
    ∑ i : Fin n, ι (φ (Pi.single i 1)) • LinearMap.proj i
  have hf (y : Fin n → E) : f (ratV (F := F) (Fv F v) y) = ι (φ y) := by
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, ratV,
      smul_eq_mul]
    change (∑ i : Fin n, ι (φ (Pi.single i 1)) * ι (y i)) = _
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  let fF := f.restrictScalars (Fv F v)
  let fO := fF.restrictScalars (v.adicCompletionIntegers F)
  have hfL : latLoc (E := E) v (L : Set (Fin n → E)) ≤ LinearMap.ker fO := by
    rw [latLoc, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change f (ratV (F := F) (Fv F v) y) = 0
    rw [hf, LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy)), map_zero]
  have hOpen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hSD (basLat_fg v L hL)
  obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v (hOpen.mem_nhds (Submodule.zero_mem _))
    (fun _ : Unit => ratV (F := F) (Fv F v) x)
  have hz := LinearMap.mem_ker.mp (hfL (htx ()))
  change fF (t • ratV (F := F) (Fv F v) x) = 0 at hz
  rw [map_smul] at hz
  change t • f (ratV (F := F) (Fv F v) x) = 0 at hz
  rw [hf] at hz
  exact ((map_ne_zero ι).2 hφx) ((smul_eq_zero.mp hz).resolve_left ht)

theorem sdVolW_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a := by
  intro hS hLat hSD hU hμ
  have hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ := by
    obtain ⟨L, hL, rfl⟩ := hLat
    exact ⟨L, fullLattice_of_isSDLoc σ J v L hL hSD, rfl⟩
  have hVol := sdVolW_of_pi σ J ψ v Λ a (condV_of_all σ J ψ v hC) (dualW_of_perf σ J ψ v Λ a hP)
    (idxPiW_std σ J ψ v Λ a hS hFull) hFull
  exact hVol hS hLat hSD hU hμ

theorem sdVolH_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) :
    SdVolH σ J ψ v a := by
  intro hS
  exact sdVolH_of_pi σ J ψ v a (condV_of_all σ J ψ v hC) (dualH_of_perf σ J ψ v a hP)
    (idxPiH_std σ J ψ v a hS) hS

end PI.OmLocU.SdB
end
end
end
