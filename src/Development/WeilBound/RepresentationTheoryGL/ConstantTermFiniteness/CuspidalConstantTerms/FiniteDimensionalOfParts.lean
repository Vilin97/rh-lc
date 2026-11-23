module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProductStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupParts
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
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommuteStatement
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesGlPart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslateStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizerStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.CoeffSpanCompMem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupPartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_parts_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r), Pairwise fun i j : Option {k // k ∈ T} => ∀ x y : GAd σ J, x ∈ part σ J X Y T i → y ∈ part σ J X Y T j → Commute x y := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.part_commute <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_variant : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, ∀ n ∈ unip D.sp.cm.sig V.gram X T, g * n * g⁻¹ ∈ unip D.sp.cm.sig V.gram X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLeviStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.levi_decomposition_hermitian_centralizer : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ mH ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ mo ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * mo = mo * t) ∧ mm = mH * mo := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLeviStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.frame_family_right_translate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ b : GA D V, IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.hermitian_part_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)), uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesUPart

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem finite_slices_uPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hWF T hT b
  obtain ⟨n, hn, mm, hmm, b₀, hb, had⟩ := GlobalTheory.T.langlands_decomposition_unipotent_levi D θ hθ V ε fr hfr m X Y hWF T b
  obtain ⟨mH, hmH, mo, hmo, hcomm, rfl⟩ := GlobalTheory.T.levi_decomposition_hermitian_centralizer D V m X Y hWF T mm hmm
  subst hb
  have hU' : IsOpen ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) =
        (fun x => b₀⁻¹ * x * b₀) ⁻¹' (U : Set (GA D V)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [mul_assoc] using hu
      · intro hx
        exact ⟨b₀⁻¹ * x * b₀, hx, by group⟩
    rw [e]
    exact hU.preimage (by fun_prop)
  have hfr' := GlobalTheory.T.frame_family_right_translate D θ hθ V ε fr hfr b₀
  have hfin := finite_slices_core D θ hθ V _ hU' ε _ hfr' W ρ hρ c m X Y hWF T hT had
  set H := uPart D.sp.cm.sig V.gram X Y T with hH
  set L := levi D.sp.cm.sig V.gram X Y T with hL
  let mH' : H := ⟨mH, hmH⟩
  let R : (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun f t => f (t * mH')
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : sliceSet (cuspOn θ V X Y T U ε fr ρ c) H L (n * (mH * mo) * b₀) ⊆
      ((Submodule.span ℂ (sliceSet (cuspOn θ V X Y T (U.map (MulAut.conj b₀).toMonoidHom) ε
        (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) ρ c) H L 1)).map R : Set (H → ℂ)) := by
    rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
    refine ⟨fun t : H => φ ((t : GA D V) * (y * mo) * b₀),
      Submodule.subset_span ⟨fun x => φ (x * b₀), GlobalTheory.T.constant_term_frame_K_type_coefficients D θ hθ V U ε fr hfr W ρ c m X Y T φ hφ b₀, y * mo,
        mul_mem hy hmo, fun t ht => ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc, hyc t ht, mul_assoc, hcomm t ht, mul_assoc]
    · funext t
      simp [mul_assoc]
    · funext t
      have ht : (t : GA D V) ∈ L := GlobalTheory.T.hermitian_part_le_levi D V m X Y T t.2
      have hty : (t : GA D V) * y ∈ L := mul_mem ht hy
      have hγ : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ ∈ unip D.sp.cm.sig V.gram X T :=
        GlobalTheory.T.levi_normalizes_unipotent_variant D V m X Y hWF T _ hty n hn
      have hleft := hφ.1.1.left _ (Subgroup.mem_sup_left hγ : _ ∈ (leftSub V X Y T : Subgroup (GA D V)))
        ((t : GA D V) * y * (mH * mo * b₀))
      have e1 : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ * ((t : GA D V) * y * (mH * mo * b₀)) =
          (t : GA D V) * y * (n * (mH * mo) * b₀) := by group
      have e2 : (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * mH * (y * mo) * b₀ := by
        have := hyc mH hmH
        calc (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * (y * mH) * mo * b₀ := by group
          _ = (t : GA D V) * (mH * y) * mo * b₀ := by rw [this]
          _ = (t : GA D V) * mH * (y * mo) * b₀ := by group
      change φ ((t : GA D V) * mH * (y * mo) * b₀) = φ ((t : GA D V) * y * (n * (mH * mo) * b₀))
      rw [← e1, hleft, e2]
  haveI := hfin
  exact Submodule.finiteDimensional_of_le (Submodule.span_le.2 hsub)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteDimensionalOfParts

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem finiteDimensional_of_parts {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (L : Subgroup G) (hgen : L = ⨆ i, H i)
    (𝓒 : Set (G → ℂ)) (B : Finset G)
    (hB : ∀ φ ∈ Submodule.span ℂ 𝓒, (∀ b ∈ B, ∀ g ∈ L, φ (g * b) = 0) → φ = 0)
    (hcore : ∀ i b, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet 𝓒 (H i) L b))) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓒) := by
  let P : (∀ i, H i) →* G := Subgroup.noncommPiCoprod hcomm
  have hrange : P.range = L := by rw [Subgroup.noncommPiCoprod_range, hgen]
  have hP : ∀ i (t : H i), P (Pi.mulSingle i t) = t := fun i t => Subgroup.noncommPiCoprod_mulSingle i t

  let R : G → (G → ℂ) →ₗ[ℂ] ((∀ i, H i) → ℂ) := fun b => LinearMap.funLeft ℂ ℂ fun x => P x * b
  have hfin : ∀ b, FiniteDimensional ℂ (Submodule.span ℂ (R b '' 𝓒)) := fun b => by
    haveI := fun i => hcore i b
    refine finiteDimensional_of_slices (fun i => Submodule.span ℂ (sliceSet 𝓒 (H i) L b)) _ ?_
    rintro _ ⟨φ, hφ, rfl⟩ i x
    have e : ∀ t : H i, Function.update x i t = Pi.mulSingle i t * Function.update x i 1 := fun t => by
      simpa only [Pi.mulSingle, one_mul, mul_one] using
        (Function.update_mul (1 : ∀ j, H j) x i t 1)
    have e' : ∀ t : H i, Function.update x i t = Function.update x i 1 * Pi.mulSingle i t := fun t => by
      simpa only [Pi.mulSingle, one_mul, mul_one] using
        (Function.update_mul x (1 : ∀ j, H j) i 1 t)
    refine Submodule.subset_span ⟨φ, hφ, P (Function.update x i 1), hrange ▸ ⟨_, rfl⟩, fun t ht => ?_, ?_⟩
    · have h1 := congrArg P ((e ⟨t, ht⟩).symm.trans (e' ⟨t, ht⟩))
      rwa [map_mul, map_mul, hP] at h1
    · funext t
      change φ (P (Function.update x i t) * b) = φ ((t : G) * P (Function.update x i 1) * b)
      rw [e t, map_mul, hP]
  have hmap : ∀ b, ∀ φ ∈ Submodule.span ℂ 𝓒, R b φ ∈ Submodule.span ℂ (R b '' 𝓒) := fun b φ hφ => by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hφ
  let Ψ : Submodule.span ℂ 𝓒 →ₗ[ℂ] (∀ b : B, Submodule.span ℂ (R b.1 '' 𝓒)) :=
    LinearMap.pi fun b => ((R b.1).comp (Submodule.span ℂ 𝓒).subtype).codRestrict _ fun φ => hmap b.1 φ.1 φ.2
  haveI := fun b : B => hfin b.1
  refine FiniteDimensional.of_injective Ψ ((injective_iff_map_eq_zero Ψ).2 fun φ hφ => ?_)
  refine Subtype.ext (hB φ.1 φ.2 fun b hb g hg => ?_)
  obtain ⟨x, rfl⟩ : g ∈ P.range := hrange ▸ hg
  exact congrFun (congrArg Subtype.val (congrFun hφ ⟨b, hb⟩)) x

theorem finite_cuspOn : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT
  classical
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨B, hB⟩ := GlobalTheory.T.archimedean_frame_K_type_decomposition D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  refine finiteDimensional_of_parts (part D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_parts_commute D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (levi D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_eq_iSup_parts D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (cuspOn θ V X Y T U ε fr ρ c) B
    (fun φ hφ h => hB φ (mem_formsOn_of_mem_span hθ (Submodule.span_mono (show cuspOn θ V X Y T U ε fr ρ c ⊆ formsOn θ V X Y T U ε fr ρ c from fun _ hf => hf.1) hφ)) h) ?_
  rintro (_ | k) b
  · exact UCore.Rg.finite_slices_uPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT b
  · exact CoreGL.Rg.finite_slices_glPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT k.1 k.2 b

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg
end
end
end
