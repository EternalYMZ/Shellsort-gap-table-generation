import Shellsort.RoughGapDenominatorAverage

/-! The short-interval high-denominator bound as a bound on actual
centered masses in the physical residue classes. -/
noncomputable section
namespace Shellsort.RoughGapResidueAverage
open Finset ZMod Shellsort.RoughGapDenominatorAverage Shellsort.RoughGapFiniteFourier

/-- Actual squared counts in residue classes, centered by the total mass / h. -/
def physicalEnergy {m : ℕ} (start : ℤ) (v : Fin m → ℝ) (h : ℕ) : ℝ :=
  if hh : 0<h then
    letI : NeZero h := ⟨hh.ne'⟩
    (h:ℝ) * ∑ r : ZMod h, (bins (fun j : Fin m ↦ (start:ZMod h)+(j.val:ZMod h)) v r - (∑ j,v j)/h)^2
  else 0

theorem actual_samples {m h : ℕ} (hh : 0<h) (start : ℤ) (v : Fin m → ℝ) :
    physicalEnergy start v h = ∑ a ∈ (range h).erase 0,
      energy start (fun j ↦ (v j:ℂ)) (a,h) := by
  classical
  let : NeZero h := ⟨hh.ne'⟩
  let col (j : Fin m) : ZMod h := (start:ZMod h)+j.val
  have raw := actual_nonzero_spectrum col v
  simp only [physicalEnergy,dite_eq_left hh]
  rw [← raw]
  have point (k : ZMod h) : Complex.normSq
      (∑ i, stdAddChar (-(col i*k)) * (v i:ℂ)) =
        energy start (fun j ↦ (v j:ℂ)) (k.val,h) := by
    rw [← Complex.sq_norm]
    unfold energy
    have term (i : Fin m) : stdAddChar (-(col i*k)) = Complex.exp
        (-2 * (Real.pi:ℂ) * Complex.I * ((start:ℂ)+i.val) * k.val / h) := by
      have lift : -(col i*k) = ((-((start+(i.val:ℤ))*(k.val:ℤ)):ℤ):ZMod h) := by
        dsimp [col]; push_cast; simp
      rw [lift,stdAddChar_coe]
      apply congrArg Complex.exp; push_cast; ring
    simp_rw [term]
  simp_rw [point]
  have inject : Set.InjOn (fun k : ZMod h ↦ k.val) (↑(univ.erase (0 : ZMod h)) : Set (ZMod h)) :=
    fun _ _ _ _ he ↦ ZMod.val_injective h he
  have imageEq : (univ.erase (0:ZMod h)).image ZMod.val = (range h).erase 0 := by
    ext x
    simp only [mem_image,mem_erase,mem_univ,and_true,mem_range]
    constructor
    · rintro ⟨k,hn,rfl⟩
      exact ⟨fun he ↦ hn (ZMod.val_injective h (by simpa using he)), k.val_lt⟩
    · rintro ⟨hne,hx⟩
      refine ⟨(x:ZMod h),?_,val_natCast_of_lt hx⟩
      intro he; have := congrArg ZMod.val he
      simp [val_natCast_of_lt hx] at this
      exact hne this
  rw [←imageEq]
  symm
  apply sum_image
  exact inject

/-- No assumed weights for repeated frequencies. G may be any sufficiently
large subset of moduli ≤2H whose prime factors are at least D. -/
theorem rough_residue_average {m H D : ℕ} (hD : 0<D) (hDH : D≤2*H)
    (G : Finset ℕ) (size : ∀ h ∈ G, 0<h ∧ h≤2*H)
    (rough : ∀ h ∈ G, ∀ p, p.Prime → p ∣ h → D≤p)
    (δ : ℝ) (hd : 0<δ) (many : δ*H≤(G.card:ℝ))
    (start : ℤ) (v : Fin m → ℝ) :
    (∑ h ∈ G, physicalEnergy start v h)/(G.card:ℝ) ≤
        (32*H+4*Real.pi*m/D)/δ * ∑ j, (v j)^2 := by
  classical
  let block := fun h : ℕ ↦ ((range h).erase 0).image (fun a ↦ (a,h))
  let S := G.biUnion block
  have encode {p : Fraction} (hp : p ∈ S) : p.2∈G ∧ 0<p.1 ∧ p.1<p.2 := by
    obtain ⟨h,hg,hr⟩ := mem_biUnion.mp hp
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hr
    simpa using ⟨hg,Nat.pos_of_ne_zero (mem_erase.mp ha).1,mem_range.mp (mem_erase.mp ha).2⟩
  have dis : (↑G : Set ℕ).PairwiseDisjoint block := by
    intro h _ k _ ne
    apply disjoint_left.mpr
    intro p hp hk
    obtain ⟨a,_,rfl⟩ := mem_image.mp hp
    obtain ⟨b,_,be⟩ := mem_image.mp hk
    exact ne (congrArg Prod.snd be).symm
  have high {p : Fraction} (hp : p∈S) : D≤(reduced p).2 := by
    obtain ⟨hg,ha,hb⟩ := encode hp
    have gg := Nat.gcd_pos_of_pos_right p.1 (Nat.zero_lt_of_lt hb)
    have ar : 0 < (reduced p).1 := Nat.div_pos
      (Nat.le_of_dvd ha (Nat.gcd_dvd_left ..)) gg
    have br : (reduced p).1 < (reduced p).2 :=
      (Nat.div_lt_div_right gg.ne' (Nat.gcd_dvd_right ..)).mpr hb
    have ne : (reduced p).2 ≠ 1 := by omega
    let d := (reduced p).2
    have prime := Nat.minFac_prime ne
    have divis : d ∣ p.2 := ⟨mult p, (Nat.div_mul_cancel (Nat.gcd_dvd_right ..)).symm⟩
    have ds := rough p.2 hg d.minFac prime ((Nat.minFac_dvd _).trans divis)
    exact ds.trans (Nat.le_of_dvd (Nat.zero_lt_of_lt br) (Nat.minFac_dvd _))
  have eq : (∑ p ∈ S, energy start (fun j ↦ (v j : ℂ)) p) =
      ∑ h ∈ G, physicalEnergy start v h := by
    rw [show S = G.biUnion block from rfl, sum_biUnion dis]
    apply sum_congr rfl; intro h hg
    rw [actual_samples (size h hg).1]
    exact sum_image (fun a _ b _ eq ↦ congrArg Prod.fst eq)
  have z := high_denominator_mean hD hDH S
    (fun p hp ↦ ⟨(encode hp).2.2,(size _ (encode hp).1).2⟩)
    (fun _ hp ↦ high hp) start (fun j ↦ (v j:ℂ)) (G.card:ℝ) δ hd many
  rw [eq] at z
  simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using z

#print axioms actual_samples
#print axioms rough_residue_average
end Shellsort.RoughGapResidueAverage

