module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.EventuallyMemLat
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceFourthLift
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.FinSumFinEquivSymmEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.PsdLeftZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BlockContinuity.ContinuousBlkAt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.ColumnAlgebra.PiColElAdd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.Stab
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.TwistedKernels.TwKerColElStable
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.NabsDetScalar

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.ULiftOfAbs

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir PositivityTheory.RgUd.Form

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem setup_tr {m N : ℕ} (h : m + 2 ≤ N) (h' : m + 1 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) :
    Setup (fun x => π (colEl k m N h x)) (π.comp (blkAt k (m + 1) N h')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp [TrM.colEl_zero]
  · intro x y v
    rw [TrM.colEl_add, map_mul, mul_apply_eq_comp]
  · intro g x v
    show π (blkAt k (m + 1) N h' g) (π (colEl k m N h x) v) =
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π (blkAt k (m + 1) N h' g) v)
    rw [← mul_apply_eq_comp, ← map_mul, TrM.blkAt_mul_colEl m N h h', map_mul, mul_apply_eq_comp]
  · intro v
    exact (hπ v).preimage (TrM.continuous_colEl m N h)
  · intro v
    exact (hπ v).preimage (TrM.continuous_blkAt (m + 1) N h')

theorem uLift_of_abs (H : @AbsLift k _ _ _ _) : PositivityTheory.RgUd.Form.U.ULift k := by
  intro ψ hψ hψ1 m N h V _ _ π hπ s B B' C A₀ hL hA₀ hD hC hCK hCM hle
  have h' : m + 1 ≤ N := by omega
  obtain ⟨hBpsd, _, hBM⟩ := hL
  have hBcol : ∀ x v w, B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
    intro x v w
    have hn : ((nabs k (GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x))) ^ s : ℝ) : ℂ) = 1 := by
      rw [TrM.det_unip_GL]
      simp [nabs]
    exact (hBM _ (MirU_le_Mir k (m + 1) (MonoidHom.mem_range.2 ⟨_, rfl⟩)) v w).trans (by rw [hn, one_mul])
  have hBgl : ∀ g v w, B ((π.comp (blkAt k (m + 1) N h')) g v) ((π.comp (blkAt k (m + 1) N h')) g w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w := by
    intro g v w
    have := hBM (glEmb k (m + 1) g) (glEmb_mem_Mir k (m + 1) g) v w
    rw [TrM.det_glEmb_GL] at this
    rw [MonoidHom.comp_apply, TrM.blkAt_glEmb (m + 1) N h' h]
    exact this
  have hCcol : ∀ x v w, C (π (colEl k m N h x) v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w := by
    intro x v w
    have hmem : π (colEl k m N h x) v -
        ((lvlChar k ψ N (m + 1) ⟨colEl k m N h x, TrM.colEl_mem m N h x⟩ : ℂˣ) : ℂ) • v ∈
          twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) :=
      Submodule.subset_span ⟨⟨_, TrM.colEl_mem m N h x⟩, v, rfl⟩
    have h0 := hCK _ hmem w
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, smul_eq_mul,
      TrM.lvlChar_colEl] at h0
    rw [h0]
    simp [xz]
  obtain ⟨I, hIpsd, hIcol, hIgl, hIle, hID, hIA, hIY⟩ := H ψ hψ hψ1 m V (fun x => π (colEl k m N h x))
    (π.comp (blkAt k (m + 1) N h')) (setup_tr h h' π hπ) s B B' C A₀ hA₀ hBpsd hBcol hBgl hD hC hCcol hCM hle
  refine ⟨I, ⟨hIpsd, ?_, ?_⟩, hIle, hID, hIA⟩
  · intro v hv w
    exact hIY (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)))
      (fun g y hy => TrM.twKer_blkAt ψ π m h' g y hy) (fun y hy w => hCK y (TrM.twKer_le_succ ψ π m hy) w) v hv w
  · intro p hp v w
    obtain ⟨x, g, rfl⟩ := TrM.mir_decomp (m + 1) p hp
    have e : ∀ u, π (blkAt k (m + 1 + 1) N h (unip k (m + 1) (Multiplicative.ofAdd x) * glEmb k (m + 1) g)) u =
        π (colEl k m N h x) (π (blkAt k (m + 1) N h' g) u) := by
      intro u
      rw [map_mul, map_mul, mul_apply_eq_comp, ← TrM.blkAt_glEmb (m + 1) N h' h]
      rfl
    rw [e, e, TrM.det_unip_mul_glEmb]
    exact (hIcol x _ _).trans (hIgl g v w)

end PositivityTheory.RgUd.Form.U.Lift2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.ULift

section

@[expose] public section

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uLift : PositivityTheory.RgUd.Form.U.ULift k := uLift_of_abs absLift

end PositivityTheory.RgUd.Form.U.Lift2
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SubquotientEigenvectors.ExistsEigenOfSubquot

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Eig

theorem exists_eigen_of_subquot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (Z : G) (c : ℂ) (hσ : ∀ w, σ Z w = c • w)
    (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ) (s : S.toSubmodule) (hs : f s ≠ 0)
    (F : Submodule ℂ V) (hfin : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, ρ Z x ∈ F) (hsF : (s : V) ∈ F) :
    ∃ x : V, x ≠ 0 ∧ ρ Z x = c • x := by
  let U : Submodule ℂ V := F ⊓ S.toSubmodule
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left
  let E : V →ₗ[ℂ] V := ρ Z - c • LinearMap.id
  have hEU : ∀ x ∈ U, E x ∈ U := by
    intro x hx
    obtain ⟨hxF, hxS⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hF x hxF) (Submodule.smul_mem _ _ hxF),
      Submodule.sub_mem _ (S.apply_mem_toSubmodule _ hxS) (Submodule.smul_mem _ _ hxS)⟩
  let E' : U →ₗ[ℂ] U := E.restrict hEU
  have hsU : (s : V) ∈ U := Submodule.mem_inf.2 ⟨hsF, s.2⟩
  have hns : ¬ Function.Surjective E' := by
    intro hsur
    obtain ⟨y, hy⟩ := hsur ⟨_, hsU⟩
    have hyS : (y : V) ∈ S.toSubmodule := (Submodule.mem_inf.1 y.2).2
    have hEy : E y = (s : V) := congrArg Subtype.val hy
    have hs' : s = S.toRepresentation Z ⟨y, hyS⟩ - c • ⟨y, hyS⟩ := by
      apply Subtype.ext
      rw [← hEy]
      rfl
    apply hs
    rw [hs', map_sub, map_smul, Representation.IntertwiningMap.isIntertwining, hσ, sub_self]
  have hni : LinearMap.ker E' ≠ ⊥ := fun h =>
    hns (LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 h))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hni
  refine ⟨(x : V), fun h => hx0 (Subtype.ext h), ?_⟩
  have hEx : ρ Z x - c • (x : V) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hx)
  exact sub_eq_zero.1 hEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_derivB (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n i : ℕ) (π : GRep k (n + i))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible (derivB ψ i π).ρ := by
  cases i with
  | zero => exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n _ π.ρ hs hi
  | succ j =>
    have hD : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π.ρ) := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs
    exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hD
      (PositivityTheory.RgGu.NR.derFin_of k (PositivityTheory.RgGu.NR.derEquiv k) ψ hc h1 n j _ π.ρ hs hi)
      fun Y _ _ τ hq hirr => PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n Y τ (hq.isSmooth hD) hirr


variable (k) in
theorem uAdm : UAdm k := fun ψ hc h1 n i π hs hi => isAdmissible_derivB ψ hc h1 n i π hs hi

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem scalar_comm (n : ℕ) (z : kˣ) (g : GL (Fin n) k) :
    g * GeneralLinearGroup.scalar (Fin n) z = GeneralLinearGroup.scalar (Fin n) z * g := by
  ext : 1
  simp only [Units.val_mul]
  exact (Algebra.commutes _ _).symm

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (x : V) : x ∈ fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp


variable (k) in
theorem uEig : UEig k := by
  intro ψ hc h1 n i π hs hi t W _ _ σ ω hW hsub hω z
  have hadm := uAdm k ψ hc h1 n i π hs hi
  obtain ⟨S, f, hf⟩ := hsub
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨s, rfl⟩ := hf w
  obtain ⟨K, hKo, hKc, hKsub⟩ := GlobalTheory.ContraProd.exists_compactOpen_GL (k := k) (Fin n)
    {g | (derivB ψ i π).ρ g s.1 = s.1}
    ((hadm.1 s.1).mem_nhds (by show (derivB ψ i π).ρ 1 s.1 = s.1; rw [map_one]; rfl))
  have hfixZ : ∀ x ∈ fixed (derivB ψ i π).ρ K, (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    rw [mem_fixed_iff] at hx ⊢
    intro h
    rw [← Module.End.mul_apply, ← map_mul, scalar_comm, map_mul, Module.End.mul_apply, hx h]
  have hF : ∀ x ∈ fixed (derivB ψ i π).ρ K,
      ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    show ((dpow n t (GeneralLinearGroup.scalar (Fin n) z) : ℂˣ) : ℂ) • (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K
    exact Submodule.smul_mem _ _ (hfixZ x hx)
  exact exists_eigen_of_subquot ((derivB ψ i π).tw t).ρ σ (GeneralLinearGroup.scalar (Fin n) z) (ω z : ℂ) (hω z) S f s hw
    (fixed (derivB ψ i π).ρ K) (hadm.2 K hKo hKc) hF ((mem_fixed_iff _ _ _).2 fun h => hKsub h.2)

end PositivityTheory.RgUd.Form.U.Eig
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryDensity.UDens

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Dens

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem uDens (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : UDens k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hB A₀ hA₀
  have hL : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hB.1, hB.2.1, hB.2.2⟩
  obtain ⟨B', hD, -⟩ := Ex.dens_exists_of hL (fun ξ A hA v w => alg.avg_selfadj hL ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hL K hK hA₀) hA₀
  exact ⟨B', hD, props.dens_psd hL hA₀ hD, props.dens_kills hL hA₀ hD, mir.dens_mir hL hA₀ hD,
    fun v hv => props.dens_rad hL hA₀ hD v hv⟩

end PositivityTheory.RgUd.Form.U.Dens
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerivPos

section

@[expose] public section

namespace PositivityTheory.RgUd.Form.U.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derivTop : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivTop k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).1

theorem derivPos : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivPos k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).2

end PositivityTheory.RgUd.Form.U.Final
end
end
