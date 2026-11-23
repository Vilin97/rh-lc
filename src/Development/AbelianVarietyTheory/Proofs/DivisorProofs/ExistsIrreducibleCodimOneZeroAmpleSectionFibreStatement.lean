module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.RingTheory.KrullDimension.Field
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducible

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KrullZero

theorem coheight_le_one {Y : Scheme.{0}} [IsLocallyNoetherian Y] {N : LB Y} (hN : N.IsLB) (t : N.Sec) (w : Y)
    (hw : w ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t)
    (hgen : ∀ y : Y, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) : Order.coheight w ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_chart hN w
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset hk
  have hle' : V ≤ N.U k := hle
  set g : Γ(Y, V) := Y.presheaf.map (homOfLE hle').op (t.f k) with hg
  have hbo : Y.basicOpen g = V ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    rw [hg, Scheme.basicOpen_res, ← GlobalTheory.nonzeroLocus_inf_chart, inf_comm _ (N.U k), ← inf_assoc,
      inf_eq_left.2 hle']
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, V), hV.fromSpec P = w := by
    have : w ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hwV
    exact this
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hmemb : ∀ Q : PrimeSpectrum Γ(Y, V), g ∈ Q.asIdeal ↔ hV.fromSpec Q ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    intro Q
    have h1 : Q ∈ PrimeSpectrum.basicOpen g ↔ hV.fromSpec Q ∈ Y.basicOpen g := by
      rw [← hV.fromSpec_preimage_basicOpen]; rfl
    have h2 : hV.fromSpec Q ∈ V := by
      have := Set.mem_range_self (f := hV.fromSpec) Q
      rwa [hV.range_fromSpec] at this
    rw [hbo] at h1
    constructor
    · intro hgQ hQ
      exact (PrimeSpectrum.mem_basicOpen _ _).1 (h1.2 ⟨h2, hQ⟩) hgQ
    · intro hQ
      by_contra hgQ
      exact hQ (h1.1 ((PrimeSpectrum.mem_basicOpen _ _).2 hgQ)).2
  have hgP : g ∈ P.asIdeal := (hmemb P).2 (hP ▸ hw)
  have hmin : P.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hgP⟩, fun Q hQ hQP => ?_⟩
    have hgQ : g ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
    by_contra hne
    let Q' : PrimeSpectrum Γ(Y, V) := ⟨Q, hQ.1⟩
    have hsp : Q' ⤳ P := (PrimeSpectrum.le_iff_specializes Q' P).1 hQP
    have hsp' : hV.fromSpec Q' ⤳ w := hP ▸ hsp.map hV.fromSpec.continuous
    have hneq : hV.fromSpec Q' ≠ w := by
      rw [← hP]
      intro h
      have := hV.fromSpec.isOpenEmbedding.injective h
      exact hne (by rw [← this])
    have hlt : w < hV.fromSpec Q' := lt_of_le_not_ge (show w ≤ hV.fromSpec Q' from hsp') fun h => hneq (hsp'.antisymm h).eq
    exact (hmemb Q').1 hgQ (hgen _ hlt)
  have hh : P.asIdeal.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  let x : Spec Γ(Y, V) := P
  have eS := (asIso (hV.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, V) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight w := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight, hP]
  have : ((Order.coheight w : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← hPh]; exact_mod_cast hh
  exact_mod_cast this

end GlobalTheory.KrullZero

namespace GlobalTheory.KrullZero


open GlobalTheory.MixHt in
theorem exists_irreducible_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C →
    (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) →
    ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧
      topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  intro k _ X _ p D hX M s C hM hC hCc hmeet hnot
  set Z := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s with hZ
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  haveI : IsNoetherian X := hamb.isNoetherian
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  have hηC : closure ({η} : Set X) = C := hη
  let i := cloι η
  have hambY : IsAmb (i ≫ p) := hamb.sub i
  haveI : IsNoetherian (clo η) := hambY.isNoetherian
  have hgi : i (genericPoint (clo η)) = η := cloι_genericPoint η
  have hWm : ∀ y : clo η, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) ↔ i y ∈ Z := fun y => by
    rw [GlobalTheory.nonzeroLocus_secPull]; rfl
  have basic := hasDim_basic k X p hamb
  have basicY := hasDim_basic k (clo η) (i ≫ p) hambY
  obtain ⟨m, hm⟩ := basicY.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo η))
  have hdY : topologicalKrullDim (clo η) = d := (basicY.2.2.2.2.2 (clo η) d).1 hd
  have hdC : topologicalKrullDim C = d := by
    have h := (basic.2.2.2.2.1 (clo η) i (genericPoint (clo η)) d).2 hd
    rw [hgi] at h
    rw [← hηC]; exact h

  have hrange : C ⊆ Set.range i := by
    rw [← hηC]
    refine closure_minimal ?_ i.isClosedEmbedding.isClosed_range
    rintro _ rfl
    exact ⟨_, hgi⟩

  obtain ⟨x, hxC, hxZ⟩ := Set.not_subset.1 hnot
  obtain ⟨y₀, rfl⟩ := hrange hxC
  have hηZ : η ∈ Z := by
    obtain ⟨x', hx'C, hx'Z⟩ := hmeet
    rw [← hηC] at hx'C
    exact (specializes_iff_mem_closure.2 hx'C).mem_open Z.isOpen hx'Z

  obtain ⟨w, hw, hwmin⟩ := (InvImage.wf (Order.coheight : clo η → ℕ∞) wellFounded_lt).has_min
    {y | y ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i)} ⟨y₀, fun h => hxZ ((hWm y₀).1 h)⟩
  obtain ⟨e, -, he⟩ := hm w
  have hce : Order.coheight w + (e : ℕ∞) = d := GlobalTheory.DimCoheight.coheight_add_eq k (clo η) (i ≫ p) hambY d hdY w e he
  have hfin : Order.coheight w < ⊤ := by
    refine lt_of_le_of_lt (le_self_add) (hce ▸ ENat.natCast_lt_top d)
  have hgen : ∀ y : clo η, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) := by
    intro y hlt
    by_contra hy
    exact hwmin y hy (Order.coheight_strictAnti hlt ((Order.coheight_anti hlt.le).trans_lt hfin))
  have h1 : Order.coheight w ≤ 1 := coheight_le_one (LB.isLB_pull hM i) (GlobalTheory.secPull s i) w hw hgen
  have h0 : Order.coheight w ≠ 0 := by
    intro h0
    have hmax : IsMax w := Order.coheight_eq_zero.1 h0
    have hsp : genericPoint (clo η) ⤳ w := genericPoint_specializes w
    have hle : genericPoint (clo η) ≤ w := hmax (show w ≤ genericPoint (clo η) from hsp)
    have heq : w = genericPoint (clo η) := (hsp.antisymm hle).eq.symm
    have hgW := (hWm (genericPoint (clo η))).2 (by rw [hgi]; exact hηZ)
    rw [← heq] at hgW
    exact hw hgW
  have hc1 : Order.coheight w = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  rw [hc1] at hce
  have hde : d = e + 1 := by
    have : ((e + 1 : ℕ) : ℕ∞) = d := by push_cast; rw [← hce, add_comm]
    exact_mod_cast this.symm
  refine ⟨closure {i w}, isIrreducible_singleton.closure, isClosed_closure, ?_, ?_⟩
  · refine closure_minimal ?_ (hCc.sdiff Z.isOpen)
    rintro _ rfl
    refine ⟨?_, fun h => hw ((hWm w).2 h)⟩
    have hs := (genericPoint_specializes w).map i.continuous
    rw [hgi] at hs
    rw [← hηC]
    exact specializes_iff_mem_closure.1 hs
  · have hC' : topologicalKrullDim (closure ({i w} : Set X)) = e := (basic.2.2.2.2.1 (clo η) i w e).2 he
    rw [hdC, hC', hde]
    push_cast
    exact le_rfl

end GlobalTheory.KrullZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducibleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C → (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧ topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  first | exact @GlobalTheory.KrullZero.exists_irreducible_zero | exact GlobalTheory.KrullZero.exists_irreducible_zero | (intros; apply GlobalTheory.KrullZero.exists_irreducible_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpen

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem dim_le_zero_of_fib_of_subset_affine : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  intro k _ X p h ℓ U C hℓ hU hC hCc hfib hCU
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  set Y := GlobalTheory.MixHt.clo η
  set i := GlobalTheory.MixHt.cloι η
  have hgen : i (genericPoint Y) = η := GlobalTheory.MixHt.cloι_genericPoint η
  have hrange : i '' Set.univ = C := by
    rw [← (genericPoint_spec Y).def, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, hgen, hη.def]
  have htop : i ⁻¹ᵁ U = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hCU (hrange ▸ Set.mem_image_of_mem i (Set.mem_univ y))
  have hV : IsAffineOpen (⊤ : Y.Opens) := htop ▸ hU.preimage i
  have hA := h.sub i
  have := hA.finite
  have : IsProper (i ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hA.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance

  have hφ := isIntegral_appTop_of_universallyClosed (i ≫ p)
  let A := Γ(Sp k, ⊤)
  let R := Γ(Y, ⊤)
  let e : A ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hAint : Algebra.IsIntegral ℤ A :=
    Algebra.IsIntegral.of_surjective e.symm.toRingHom.toIntAlgHom e.symm.surjective
  letI : Algebra A R := (i ≫ p).appTop.hom.toAlgebra
  have hRA : Algebra.IsIntegral A R := ⟨hφ⟩
  have hRint : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.trans A

  have hchar : ((ℓ : ℕ) : R) = 0 := by
    have hcX : CharP (X.residueField η) ℓ := ringChar.eq_iff.mp (hfib hη.mem)
    have h1 : ((ℓ : ℕ) : X.residueField (i (genericPoint Y))) = 0 := by
      rw [hgen]; exact CharP.cast_eq_zero _ ℓ
    have h2 : ((ℓ : ℕ) : Y.residueField (genericPoint Y)) = 0 := by
      have := congrArg (i.residueFieldMap (genericPoint Y)).hom h1
      simpa using this
    have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
      (RingHom.injective (Y.residue (genericPoint Y)).hom).comp
        (germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial)
    apply hinj
    simpa using h2

  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP R ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hchar
  letI : Algebra (ZMod ℓ) R := ZMod.algebra R ℓ
  have : Algebra.IsIntegral (ZMod ℓ) R := Algebra.IsIntegral.tower_top ℤ
  have hR : IsField R := isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))

  have hdimY : topologicalKrullDim ((⊤ : Y.Opens) : Set Y) = 0 := by
    rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans (ringKrullDim_eq_zero_of_isField hR)
  rw [← hrange, GlobalTheory.MixHt.DimBasic.dim_image i.isClosedEmbedding.isEmbedding]
  rw [TopologicalSpace.Opens.coe_top] at hdimY
  exact hdimY.le

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpenStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  first | exact @GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | exact GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | (intros; apply GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibre

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.AmpleCut

theorem le_of_succ_le_add_one {x : WithBot ℕ∞} {d : ℕ} (h : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ x + 1) :
    (d : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have : d + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d ≤ n)

theorem exists_irreducible_diff_NV : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime →
    IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e →
    f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  intro k _ X _ p D hX P hA ℓ d e C f hℓ hCi hCc hCf hdim he hf
  by_cases h0 : C ∩ NV P e 0 f = ∅
  · refine ⟨C, hCi, hCc, fun x hx => ⟨hx, fun hx' => ?_⟩, ?_⟩
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) x ⟨hx, hx'⟩
    · exact le_trans (by exact_mod_cast Nat.le_succ d) hdim
  obtain ⟨u, hu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P e).2 f hf
  have hisP : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have hne : (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)).Nonempty := by
    rw [← hu]; exact Set.nonempty_iff_ne_empty.2 h0
  by_cases hsub : C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)
  · exfalso
    have haff := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
    have h1 := GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) ℓ _ C hℓ haff hCi hCc hCf hsub
    have h2 := hdim.trans h1
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h2
    have := WithBot.coe_le_coe.1 this
    norm_cast at this
  · obtain ⟨C', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible k X p D hX (lbPow P.L.B e) u C (isLB_lbPow hA.isLB e) hCi hCc hne hsub
    refine ⟨C', h1, h2, ?_, le_of_succ_le_add_one (hdim.trans h4)⟩
    rw [hu]; exact h3

end GlobalTheory.AmpleCut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e → f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧ (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  first | exact @GlobalTheory.AmpleCut.exists_irreducible_diff_NV | exact GlobalTheory.AmpleCut.exists_irreducible_diff_NV | (intros; apply GlobalTheory.AmpleCut.exists_irreducible_diff_NV <;> assumption)
end
end
