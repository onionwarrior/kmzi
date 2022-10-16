#include <array>
#include <bitset>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <format>
#include <tuple>
#include <utility>
#include <vector>
template <typename source, template <typename...> class TargetT>
struct list_rename_as_impl;

template <template <typename...> class SourceT, typename... Args,
          template <typename...> class TargetT>
struct list_rename_as_impl<SourceT<Args...>, TargetT> {
    using type = TargetT<Args...>;
};

template <typename source, template <typename...> class TargetT>
using list_rename_as_t = typename list_rename_as_impl<source, TargetT>::type;

template <typename...> struct list;
template <typename, typename> struct list_append_impl;
template <typename... Ts, typename... Us>
struct list_append_impl<list<Ts...>, list<Us...>> {
    using type = list<Ts..., Us...>;
};

template <template <typename> class, typename...> struct filter_impl;

template <template <typename> class Predicate> struct filter_impl<Predicate> {
    using type = list<>;
};

template <template <typename> class Predicate, typename T, typename... Rest>
struct filter_impl<Predicate, T, Rest...> {
    using type = typename list_append_impl<
        std::conditional_t<Predicate<T>::value, list<T>, list<>>,
        typename filter_impl<Predicate, Rest...>::type>::type;
};

template <template <typename> class Predicate, typename... Ts>
using filter = typename filter_impl<Predicate, Ts...>::type;

template <class...> using void_t = void;

template <class, class, class = void>
constexpr bool is_output_iterator_v = false;

template <class I, class E>
constexpr bool is_output_iterator_v<
    I, E,
    void_t<typename std::iterator_traits<I>::iterator_category,
           decltype(*std::declval<I>() = std::declval<E>())>> = true;
constexpr std::size_t operator""_zu(unsigned long long x) { return x; }

using block = std::bitset<32>;
using half_block = std::bitset<16>;
using byte = std::bitset<8>;
using four_bits = std::bitset<4>;

constexpr static half_block operator""_hb(unsigned long long v) {
    return half_block{static_cast<std::uint16_t>(v)};
}

template <size_t A, size_t B>
std::bitset<A + B> concat(const std::bitset<A> &l, const std::bitset<B> &r) {
    return std::bitset<A + B>(l.to_string() + r.to_string());
}

template <size_t N> auto rotl(const std::bitset<N> &bits, std::size_t count) {
    count %= N;
    return (bits << count) | (bits >> (N - count));
}

template <std::size_t N>
std::pair<std::bitset<N / 2>, std::bitset<N / 2>>
halve(const std::bitset<N> &b) {
    std::bitset<N / 2> l = 0, r = 0;
    for (auto i = 0_zu; i < N / 2; ++i) {
        l[i] = b[i];
        r[i] = b[N / 2 + i];
    }
    return {r, l}; //�������?
}
struct no_key_required {};
// type = key type

template <std::uint8_t A, std::uint8_t B, std::uint8_t... Args> struct sp16 {
    constexpr static std::uint8_t sbox[]{Args...};
    half_block operator()(half_block b, half_block key) const {
        b ^= key;
        constexpr auto hw_size = b.size();
        half_block ret = 0;
        for (auto i = 0_zu; i < hw_size; i += 4) {
            four_bits slice = 0;
            for (auto idx = 0; idx < 4; idx++) {
                slice[idx] = b[i + idx];
            }
            const four_bits replaced =
                sbox[static_cast<std::uint8_t>(slice.to_ulong())];

            for (auto idx = 0; idx < 4; idx++) {
                ret[idx + i] = replaced[idx];
            }
        }
        b = 0;
        for (std::size_t i = 0; i < hw_size; ++i)
            b[(A * i + B) % hw_size] = ret[i];
        return b;
    }
};

// emulate typelist
template <std::uint8_t A, std::uint8_t B, std::uint8_t... Args> struct sp {
    constexpr static std::uint8_t sbox[]{Args...};
    static_assert(sizeof...(Args) == 16);
    using type = block;
    block operator()(block b, const type &key) const {
        b ^= key;
        constexpr auto hw_size = b.size();
        block ret = 0;
        for (auto i = 0_zu; i < hw_size; i += 4) {
            four_bits slice = 0;
            for (auto idx = 0; idx < 4; idx++) {
                slice[idx] = b[i + idx];
            }
            const four_bits replaced =
                sbox[static_cast<std::uint8_t>(slice.to_ulong())];

            for (auto idx = 0; idx < 4; idx++) {
                ret[idx + i] = replaced[idx];
            }
        }
        b = 0;
        for (std::size_t i = 0; i < hw_size; ++i)
            b[(A * i + B) % hw_size] = ret[i];
        return b;
    }
};
template <std::uint8_t A, std::uint8_t B, std::uint8_t... Args> struct f_op {

    sp16<A, B, Args...> sp16_;
    using type = half_block;
    block operator()(const block b, const type &key) const {
        auto &&[lhw, rhw] = halve(b);
        return concat(rhw, lhw ^ sp16_(rhw, key));
    }
};

template <std::uint8_t A, std::uint8_t B, std::uint8_t... Args> struct l_op {
    sp16<A, B, Args...> sp16_;
    using type = half_block;
    block operator()(const block b, const type &key) const {
        auto &&[lhw, rhw] = halve(b);
        return concat(lhw ^ sp16_(lhw ^ rhw, key), rhw ^ sp16_(lhw ^ rhw, key));
    }
};
struct w {
    using type = block;
    block operator()(const block b, const type &key) const { return b ^ key; }
};
struct t {
    using type = no_key_required;
    block operator()(const block b, const type key) const {
        auto &&[l, r] = halve(b);
        return concat(r, l);
    }
};

template <std::size_t... S> struct seq {};
template <std::size_t N, std::size_t... S>
struct gens : gens<N - 1, N - 1, S...> {};
template <template <typename...> class Tup1, template <typename...> class Tup2,
          typename... A, typename... B, std::size_t... S>
auto tuple_zip_helper(Tup1<A...> t1, Tup2<B...> t2, seq<S...> s)
-> decltype(std::make_tuple(std::make_pair(std::get<S>(t1),
                                           std::get<S>(t2))...)) {
    return std::make_tuple(std::make_pair(std::get<S>(t1), std::get<S>(t2))...);
}

template <std::size_t... S> struct gens<0, S...> { typedef seq<S...> type; };
template <template <typename...> class Tup1, template <typename...> class Tup2,
          typename... A, typename... B>
auto tuple_zip(Tup1<A...> t1, Tup2<B...> t2)
-> decltype(tuple_zip_helper(t1, t2, typename gens<sizeof...(A)>::type())) {
    static_assert(sizeof...(A) == sizeof...(B),
        "The tuple sizes must be the same");
    return tuple_zip_helper(t1, t2, typename gens<sizeof...(A)>::type());
}

template <typename T> struct tuple_transform;
template <class... TupleTypes>
struct tuple_transform<std::tuple<TupleTypes...>> {
    using type = std::tuple<typename TupleTypes::type...>;
};
template <typename T>
using tuple_transform_t = typename tuple_transform<T>::type;

template <typename T> struct needs_round_key : std::bool_constant<true> {};
template <> struct needs_round_key<t> : std::bool_constant<false> {};

template <typename Mode> struct base_mode {
    [[nodiscard]] block encrypt(const block b) const {
        return static_cast<const Mode *>(this)->encrypt_impl(b);
    }
};

template <typename Encryption,typename Counter> struct ctr_mode : base_mode<ctr_mode<Encryption,Counter>> {
    Counter ctr_;
    Encryption enc_;
    explicit ctr_mode(Encryption &&enc, Counter &&ctr)
        : ctr_{std::forward<Counter>(ctr)},
          enc_{std::forward<Encryption>(enc)}
    {}

    [[nodiscard]] block encrypt_impl(const block b) const { return b^enc_(ctr_()); }
};

template <class... RoundActions> struct cryptosystem {
    using round_operations = std::tuple<RoundActions...>;
    using round_keys = tuple_transform_t<round_operations>;
    using rounds = decltype(tuple_zip(std::declval<round_operations>(),
                                      std::declval<round_keys>()));
    round_operations round_operations_{};
    round_keys keys_;   
    rounds rounds_;
    block encrypt(block b) {
        auto assign = [&b](auto &&val) { b = val; };
        std::apply(
            [&b, &assign](auto &&...t) { (assign(t.first(b, t.second)), ...); },
            rounds_);
        return b;
    }
    template <typename InIt,typename Mode>
    void encrypt(InIt beg, InIt end,const base_mode<Mode>& mode) {
        while (beg != end) {
            *beg= mode.encrypt(*beg);
            ++beg;
        }
    }
    template <typename... Keys>
    explicit cryptosystem(Keys... keys)
        : keys_{keys...}, rounds_{tuple_zip(round_operations_, keys_)} {
        static_assert(std::tuple_size_v<list_rename_as_t<
                filter<needs_round_key, RoundActions...>, std::tuple>>,
            "Not enough keys");
    }
};

#define SET_CRYPTO_PARAM(...)                                                  \
  using s = sp<__VA_ARGS__>;                                                   \
  using f = f_op<__VA_ARGS__>;                                                 \
  using l = l_op<__VA_ARGS__>;


SET_CRYPTO_PARAM(31,5,5, 13, 2, 8, 10, 12, 11, 15, 0, 7, 14, 6, 9, 1, 3, 4)
namespace fs = std::filesystem;
block read_key(const fs::path &p) {
    std::ifstream file{p, std::ios::binary};

    std::vector<std::uint8_t> key{std::istreambuf_iterator<char>{file},
        std::istreambuf_iterator<char>{}};
    const auto key_size = key.size();
    std::vector<half_block> helper;
    for (auto i = 0_zu; i < key.size(); i += 2) {
        helper.push_back(concat(byte{key[i]}, byte{key[i + 1]}));
    }
    return concat(helper[0], helper[1]);
}
std::vector<block> read_from_file(const fs::path &p) {
    std::ifstream file{p, std::ios::binary};

    std::vector<std::uint8_t> dt{std::istreambuf_iterator<char>{file},
        std::istreambuf_iterator<char>{}};
    const auto inp = dt.size();
    if (inp % 4 != 0) {

        dt.insert(std::end(dt) /*std::begin(dt) + whole_blocks * 4 + 1*/, 0x80);
        for (auto i = 0_zu; i < 3 - inp % 4; ++i) {
            dt.insert(std::end(dt) /*std::begin(dt) + whole_blocks * 4 + 1*/, 0x0);
        }
    }
    std::vector<half_block> helper;
    std::vector<block> ret;
    for (auto i = 0_zu; i < dt.size(); i += 2) {
        helper.push_back(concat(byte{dt[i]}, byte{dt[i + 1]}));
    }
    for (auto i = 0_zu; i < helper.size(); i += 2) {
        ret.push_back(concat(helper[i], helper[i + 1]));
    }
    if (inp % 4 == 0) {
        ret.emplace_back(std::uint32_t{1} << 31);
    }
    return ret;
}
int main() {
    
    std::vector<block> encrypted;
    for (auto i =1;i<=10;i++)
    {
        constexpr auto _ = no_key_required{};
        auto data = read_from_file(std::format("C:\\test_cases\\test{}.in",i));
        auto &&[k1, k2] = halve(read_key(std::format("C:\\test_cases\\key{}.in",i)));
        cryptosystem<l, s,t,f,f> sys{
            rotl(k2,14),
            concat(rotl(k1,9)^(k2^31798_hb), (rotl(k2, 3))),
            _,
            k1,
            k2};
        //pass block here
        auto counter = [iv = read_key("")]() mutable
        {
            iv = (340660715*iv.to_ulong() + 535838461);
            return iv;
        };
        auto mode = ctr_mode(
            [&sys](auto&& block) { return sys.encrypt(block); }, std::ref(counter));
        sys.encrypt(std::begin(data), std::end(data),mode);
        std::ofstream out{std::format("C:\\test_results\\test{}.out",i), std::ios::binary};
        std::vector<std::uint32_t> binary_out;
        std::ranges::transform(data,
                               std::back_inserter(binary_out), [](auto &&v) {
                                   const auto val = v.to_ulong();
                                   return (
                                       (((val)&0xff000000) >> 24) | (((val)&0x00ff0000) >> 8) |
                                       (((val)&0x0000ff00) << 8) | (((val)&0x000000ff) << 24));
                               });
        out.write(reinterpret_cast<const char *>(binary_out.data()),
                  binary_out.size() * sizeof(std::uint32_t));
    }
    return 0;
}
