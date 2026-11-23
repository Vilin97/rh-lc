module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenFree
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenLevel
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealTraceMap
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingIndex
import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.ProfiniteCohomology.RealPlaces.Induced
public import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import GroundTheory.ProfiniteCohomology.PoincarePairs.MackeyCup
public import GroundTheory.ProfiniteCohomology.RealPlaces.DevissageDefs
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
public import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.ProfiniteCohomology.PoincarePairs
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealCup
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenFree
public import GroundTheory.ProfiniteCohomology.RealPlaces.Devissage
public import GroundTheory.ProfiniteCohomology.RealPlaces.Vanishing
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenTau

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

def GsTauBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) : Prop :=
  letI : IsDiscreteRep (gsRoots S N) := isDiscreteRep_gsRoots S N
  letI := isDiscreteRep_res_subtype (gsRoots S N) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
  ∀ τ : compactCohomologyRes (mackeyFamily U (gsFinFamily S ιs))
      (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) 3 →+ ZMod N,
    Function.Surjective τ → ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactZmodDualityMap (mackeyFamily U (gsFinFamily S ιs))
        (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) (nsmul_gsRoots S N) τ h)



include hS hev in
theorem gsTauBijective_gsOpenSubgroup {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : GsTauBijective S ιs (N := N) (gsOpenSubgroup S hL) := by
  intro τ hτ r s h
  have hTC := isTotallyComplex_of_gsOpenSubgroup_le S hS hev hL W₀ hW₀ hU
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((N : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  -- The conclusion converts to the goal without unfolding the cohomology constructions.
  with_reducible
    exact bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective S ιs hL N τ hτ _
      (gsLevelBijective_gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) hSL (Or.inr hTC)) h

end GroundTheory.ProfCoh
end
end
end

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenCoind

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (U : OpenSubgroup G) (hU : FreeOnCosets ψ (U : Subgroup G))

section Shapiro

theorem tateCoindIso_tateCompactCupRes {N₁ N₂ N₃ : Rep (ULift.{0} ℤ) (U : Subgroup G)} [IsDiscreteRep N₁]
    [IsDiscreteRep N₂] [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃) {a r b : ℕ} (h : (a + 1) + r = b + 1)
    (y : tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N₁) (a + 1))
    (x : cohomology (Rep.coind (U : Subgroup G).subtype N₂) r) :
    (tateCoindIso φ ψ U N₃ hU b).hom.hom (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x) =
      compactCupRes (mackeyFamily U φ) μ h ((tateCoindIso φ ψ U N₁ hU a).hom.hom y)
        ((shapiroMap U N₂ r).hom x) := by
  rw [tateCoindIso_hom, tateCoindIso_hom]
  change (mackeyCompactCohomologyIso U φ N₃ (b + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (b + 1)).hom
        (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x)) =
    compactCupRes (mackeyFamily U φ) μ h ((mackeyCompactCohomologyIso U φ N₁ (a + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (a + 1)).hom y)) ((shapiroMap U N₂ r).hom x)
  rw [tateForget_tateCompactCupRes]
  exact mackeyCompactCohomologyIso_compactCupRes U φ μ h _ x

theorem tateCompactCores_tateCoindIso_hom (A : Rep (ULift.{0} ℤ) G) [IsDiscreteRep A] (b : ℕ)
    (W : tateCompactCohomologyRes φ ψ
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) (b + 1)) :
    (tateCompactCores φ ψ U hU A b).hom
        ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W) =
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom W := by
  change (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom
    ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).inv.hom
      ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W)) = _
  rw [hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom_inv_id W]
  rfl

end Shapiro

section Coind

variable {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

def tateCoindDualCompactMap (s : ℕ) :
    tateCompactCohomologyRes φ ψ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1) →+
      compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) (s + 1) :=
  ((compactCohomologyResMap (mackeyFamily U φ)
      (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom.comp
    (((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom).comp
      (tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom)).toAddMonoidHom

theorem tateCoindDualCompactMap_apply (s : ℕ)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCoindDualCompactMap φ ψ U hU hD s y =
      (compactCohomologyResMap (mackeyFamily U φ)
        (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom
        ((tateCoindIso φ ψ U
          (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
          ((tateCompactCohomologyResMap φ ψ
            (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y)) :=
  rfl

theorem bijective_tateCoindDualCompactMap (s : ℕ) :
    Function.Bijective (tateCoindDualCompactMap φ ψ U hU hD s) := by
  have h1 := bijective_compactCohomologyResMap_of_comp_eq_id (mackeyFamily U φ)
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).inv (Iso.hom_inv_id _)
    (Iso.inv_hom_id _) (s + 1)
  have h2 : Function.Bijective (tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(tateCoindIso φ ψ U _ hU s).inv.hom,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).hom_inv_id w,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).inv_hom_id w⟩
  have h3 := bijective_tateCompactCohomologyResMap_of_comp_eq_id φ ψ
    (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualInv_comp_coindDualHom _ _ _) (coindDualHom_comp_coindDualInv _ _ _) (s + 1)
  exact h1.comp (h2.comp h3)

abbrev tateCoresTrace (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) :
    compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) 3 →+ ZMod n :=
  t.comp (tateCompactCores φ ψ U hU D 2).hom.toAddMonoidHom

theorem tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (x : cohomology (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) r)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCompactDualityMap φ ψ D h t
        (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) x y =
      compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) hD
        (tateCoresTrace φ ψ U hU t) h ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
        (tateCoindDualCompactMap φ ψ U hU hD s y) := by
  have hy : (tateCompactCohomologyResMap φ ψ (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
      (s + 1)).hom ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) = y := by
    rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp,
      coindDualInv_comp_coindDualHom, tateCompactCohomologyResMap_id]
    rfl
  have e1 := compactCupRes_compactCohomologyResMap (mackeyFamily U φ)
    (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (𝟙 _)
    (by rw [tensorHom_zmodDualIso_zmodMulPairingRight, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y))
    ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e1
  have e2 := tateCoindIso_tateCompactCupRes φ ψ U hU
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (b := 2) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x
  have e3 := tateCompactCores_tateCoindIso_hom φ ψ U hU D 2
    (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G)
      (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)))
      ((Nat.add_comm (s + 1) r).trans h)
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x)
  rw [tateCompactDualityMap_apply, compactZmodDualityMap_apply, tateCoindDualCompactMap_apply, e1, ← e2]
  refine Eq.trans (congrArg t ?_) (congrArg t e3).symm
  conv_lhs => rw [← hy]
  rw [tateCompactCupRes_tateCompactCohomologyResMap φ ψ _
    ((coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D ⊗ₘ
      𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)))
    _ (𝟙 _) (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]), cohomologyMap_id,
    tensorHom_coindDualHom_dualEvalPairing, ← tateCompactCohomologyResMap_tateCompactCupRes]
  rfl

theorem bijective_tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (hb : Function.Bijective (compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D)
      hD (tateCoresTrace φ ψ U hU t) h)) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) := by
  have hsh : Function.Bijective (shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r) :=
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap U _ r), inv_shapiroMap_apply U r,
      shapiroMap_inv_apply U r⟩
  exact bijective_of_bijective_comp hb hsh (bijective_tateCoindDualCompactMap φ ψ U hU hD s)
    (tateCompactDualityMap_coind φ ψ U hU hD t h)

end Coind

section Cores

theorem surjective_tateCompactCores_three (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D] [Finite D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (tateCompactCohomologyRes φ ψ M 4)) :
    Function.Surjective (tateCompactCores φ ψ U hU D 2).hom := by
  have hS := coindTraceShortComplex_shortExact (U : Subgroup G) D
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)))
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    isDiscreteRep_subrepresentation _ _ _
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₃ := inferInstanceAs (IsDiscreteRep D)
  have : Finite (Rep.res (U : Subgroup G).subtype D) := inferInstanceAs (Finite D)
  have : Finite (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)) :=
    finite_coind U _
  have : Finite (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    inferInstanceAs (Finite (coindTraceKer (U : Subgroup G) D))
  have hN : ∀ m : (coindTraceShortComplex (U : Subgroup G) D).X₁, n • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hD _))
  have h4 := hV _ hN
  have hg : Function.Surjective
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) D) 3).hom := fun y =>
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (tateCompactRes_exact₃ φ ψ hS 3)
      (@Subsingleton.elim _ h4 _ _)
  intro y
  refine (hg y).elim fun x hx => ⟨(tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype D) hU 2).hom.hom x, ?_⟩
  exact (tateCompactCores_tateCoindIso_hom φ ψ U hU D 2 x).trans hx

end Cores

end GroundTheory.ProfCoh
end
end
end

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenHyp

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Hypotheses

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)


include hS hev in
theorem gsTauBijective_of_le (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) : GsTauBijective S ιs (N := N) U := by
  obtain ⟨L, _, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S U
  exact gsTauBijective_gsOpenSubgroup S ιs hS hev hL W₀ hW₀ hU



include hS hev in
theorem bijective_tateCompactDualityMap_coind_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) {r s : ℕ} (h : r + (s + 1) = 3)
    [IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)))] :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t
      (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := by
  have hfree := freeOnCosets_gsRealFamily_of_le S ιr hS hev W₀ hW₀ U hU
  refine bijective_tateCompactDualityMap_coind (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree
    (nsmul_gsRoots S N) t h ?_
  have : Finite (gsRoots S N) :=
    (nonempty_addEquiv_gsRoots_of_mem S hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm
  have hτ : Function.Surjective (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) :=
    ht.comp (surjective_tateCompactCores_three (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree (gsRoots S N)
      (nsmul_gsRoots S N) fun M _ _ hM => subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM
        le_rfl)
  have hb := gsTauBijective_of_le S ιs hS hev W₀ hW₀ U hU
    (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) hτ h
  convert hb using 1


include hS hev in
theorem exists_tateCompactDualityHypotheses_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      TateCompactDualityHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) N (gsRoots S N) t U₀ := by
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S (2 * N) hn0
  refine ⟨W₀, ⟨nonempty_addEquiv_gsRoots_of_mem S hS, fun M _ _ hM =>
    subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM le_rfl, fun U hU {r s} h hs => ?_⟩⟩
  cases s with
  | zero => exact absurd hs (by norm_num)
  | succ s =>
    have : Finite (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)) := finite_coind U _
    have : IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := isDiscreteRep_dualRep _ _
    convert bijective_tateCompactDualityMap_coind_gs_of_even S ιr ιs hS hev t ht W₀ hW₀ U hU h using 1


include hS hev in
theorem bijective_tateCompactDualityMap_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t M) :=
  (exists_tateCompactDualityHypotheses_gs_of_even S ιr ιs hS hev t ht).elim fun _ H =>
    H.bijective_tateCompactDualityMap M hM h hs


include hS hev in
theorem gsEvenTatePoitouTateHypotheses :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsTrace S ιr ιs N) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  have : Nonempty S := nonempty_of_natCast_mem S 2 Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have ht := surjective_of_localToCompact_two S ιr ιs hS (gsTrace S ιr ιs N) (gsTrace_localToCompact S ιr ιs N)
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs =>
        bijective_tateCompactDualityMap_gs_of_even S ιr ιs hS hev (gsTrace S ιr ιs N) ht M hM h hs
      finite_cohomology := fun M _ _ hM r hr =>
        finite_cohomology_gs K S M (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
      localToCompact_two := gsTrace_localToCompact S ιr ιs N
      injective_res_zero := fun M _ => injective_ptRes_zero_gs S ιs M
      surjective_localPairing_zero := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_localPairing_two := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_realPairing_zero := fun M _ _ hM w => surjective_gsRealPairing_zero S ιr N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ => exists_gsRealPairing_two S ιr N M hD hM w χ hχ }

end Hypotheses

end GroundTheory.ProfCoh
end
end
end
