#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <bits/stdc++.h>

const uint32_t TOP_N = 100;
const uint32_t THREAD_SIZE = 8;
const uint32_t EDGE_SIZE = 250'0000;
const uint32_t PRE_SERVE_SIZE = 100'0000;
const uint32_t NODE_SIZE = EDGE_SIZE * 2;
//const char* const INPUT = "../test_data.txt";
//const char* const OUTPUT = "../my_result.txt";
const char* const INPUT = "/data/test_data.txt";
const char* const OUTPUT = "/projects/student/result.txt";
const double eps = 1e-4;

const uint64_t POOL_SIZE = 1073741824ull * 2ull;
inline void* alloc(uint32_t bytes) {
    static char pool[POOL_SIZE], *finish = pool;
    void* result = finish;
    finish += bytes;
    return result;
}

template <class T>
inline T* alloc(uint32_t n) {
    return (T*)alloc(n * sizeof(T));
}

template <class T>
struct Vector {
    using pointer = T *;
    using reference  = T &;
    using const_pointer = const T *;
    using const_reference = const T &;

    Vector() : __begin(nullptr), __end(nullptr) {}

    explicit Vector(uint32_t n) noexcept { expend(n); }

    explicit Vector(uint32_t n, T x) {
        assign(n, x);
    }

    pointer begin() { return __begin; }

    pointer end() { return __end; }

    const_pointer begin() const { return __begin; }

    const_pointer end() const { return __end; }

    void clear() { __end = __begin; }

    uint32_t size() const { return __end - __begin; }

    void reserve(uint32_t n) {
        __begin = alloc<T>(n);
        __end = __begin;
    }

    void assign(uint32_t n, T x) {
        expend(n);
        std::fill(__begin, __end, x);
    }

    void push_back(const T &x) {
        *__end++ = x;
    }

    void push_back(T &&x) {
        *__end++ = std::move(x);
    }

    template<class ...Args>
    void emplace_back(Args &&...args) {
        ::new(__end++)(T)(args...);
    }

    void erase(pointer first, pointer last) {
        if (last == __end)
            __end = first;
        else {
            fprintf(stderr, "Vector::erase is not implemented!\n");
            exit(EXIT_FAILURE);
        }
    }

    reference operator[](uint32_t i) { return __begin[i]; }

    const_reference operator[](uint32_t i) const { return __begin[i]; }

private:
    pointer __begin, __end;

    void expend(uint32_t n) noexcept {
        __begin = alloc<T>(n);
        __end = __begin + n;
    }
};

struct BufferedReader {
    explicit BufferedReader(const char* const file_name) noexcept
            : fd(open(file_name, O_RDONLY)), iter(0), length(size(fd))
            , buffer((char*)mmap(nullptr, length, PROT_READ, MAP_PRIVATE, fd, 0)) {
    }
    static inline int size(int fd) {
        FILE* file = fdopen(fd, "r");
        fseek(file, 0, SEEK_END);
        return (int)ftell(file);
    }
    bool has_next() {
        while (iter < length && !isdigit(buffer[iter]))
            ++iter;
        return iter != length;
    }
    uint32_t next_int() {
        uint32_t number = 0;
        char ch = get();
        while (!isdigit(ch)) ch = get();
        for (; isdigit(ch); ch = get())
            number = number * 10 + ch - '0';
        return number;
    }
    void close() {
        ::close(fd);
    }
    char get() {
        return iter == length ? EOF : buffer[iter++];//NOLINT
    }
    int fd, iter, length;
    char * buffer;
} reader(INPUT);

struct InputEdge {
    uint32_t from, to, cost;
};

template <class Cost>
struct Node {
    uint32_t to;
    Cost cost;
};

template <class Dist, class Cost>
struct RunnerBase {
    const Vector<Vector<Node<Cost>>> &G;
    const Vector<uint32_t> &power;
    Vector<double> &center;

    Vector<Vector<uint32_t>> prev;
    Vector<Dist> dist;
    Vector<uint16_t> count;
    Vector<uint32_t> order;
    Vector<double> delta;

    explicit RunnerBase(const Vector<Vector<Node<Cost>>> &G, Vector<double> &center, const Vector<uint32_t> &in_degree,
                        const Vector<uint32_t> &power)
            : G(G), center(center), prev(G.size()), dist(G.size(), std::numeric_limits<Dist>::max()),
              count(G.size()), delta(G.size()), power(power) {
        for (uint32_t i = 0; i < G.size(); i++) {
            prev[i].reserve(in_degree[i]);
        }
        order.reserve(G.size());
    }

    void calculate(uint32_t s) {
        for (uint32_t i = order.size(); 1 < i; i--) {
            uint32_t u = order[i - 1];
            delta[u] *= count[u];
            const double tmp = (1 + delta[u]) / count[u];
            for (const uint32_t v : prev[u]) {
                delta[v] += tmp;
            }
            dist[u] = std::numeric_limits<Dist>::max();
            center[u] += delta[u] * power[s];
            delta[u] = 0;
        }
        dist[order[0]] = std::numeric_limits<Dist>::max();
        delta[order[0]] = 0;
        center[s] += 1.0 * (power[s] - 1) * (order.size() - 1);
    }
};

struct RadixHeap {
    static const uint32_t BUCKET_SIZE = std::numeric_limits<uint64_t>::digits + 1;
    static inline uint32_t get_bucket(uint64_t x) {
        return x == 0 ? 0 : 64 - __builtin_clzll(x);
    }
    RadixHeap() {
        std::fill(minimum, minimum + BUCKET_SIZE, std::numeric_limits<uint64_t>::max());
        for (auto &item : bucket)
            item.reserve(PRE_SERVE_SIZE);
    }
    void push_zero(uint32_t value) {
        last = 0;
        bucket[0].emplace_back(0, value);
    }
    void push(uint64_t key, uint32_t value) {
        const uint32_t p = get_bucket(key ^ last);
        bucket[p].emplace_back(key, value);
        minimum[p] = std::min(minimum[p], key);
    }
    void pull() {
        uint32_t i = 1;
        for (; bucket[i].empty(); i++);
        last = minimum[i];
        for (const auto& it : bucket[i]) {
            push(it.first, it.second);
        }
        bucket[i].clear();
        minimum[i] = std::numeric_limits<uint64_t>::max();
    }
    std::pair<uint64_t, uint32_t> pop() {
        if (bucket[0].empty()) {
            pull();
        }
        auto result = bucket[0].back();
        bucket[0].pop_back();
        return result;
    }
    uint64_t minimum[BUCKET_SIZE], last;
    std::vector<std::pair<uint64_t, uint32_t>> bucket[BUCKET_SIZE];
};

struct RadixHeapImpl: RunnerBase<uint64_t, uint32_t> {
    explicit RadixHeapImpl(const Vector<Vector<Node<uint32_t>>> &G, Vector<double> &center,
                           const Vector<uint32_t> &in_degree,
                           const Vector<uint32_t> &power) : RunnerBase<uint64_t, uint32_t>(G, center, in_degree,
                                                                                           power) {}

    RadixHeap q;

    void operator()(uint32_t s) {
        q.push_zero(s);
        dist[s] = 0;
        count[s] = 1;
        order.clear();
        for (uint32_t size = 1; size != 0; size--) {
            const auto[least, node] = q.pop();
            if (least != dist[node])
                continue;
            order.push_back(node);
            for (const auto &edge : G[node]) {
                if (least + edge.cost < dist[edge.to]) {
                    dist[edge.to] = least + edge.cost;
                    count[edge.to] = count[node];
                    prev[edge.to].clear();
                    prev[edge.to].push_back(node);
                    q.push(dist[edge.to], edge.to);
                    size++;
                } else if (least + edge.cost == dist[edge.to]) {
                    count[edge.to] += count[node];
                    prev[edge.to].push_back(node);
                }
            }
        }
        calculate(s);
    }
};

template <uint32_t BUCKET_SIZE>
struct CircularQueueImpl : RunnerBase<uint16_t, uint8_t> {
    explicit CircularQueueImpl(const Vector<Vector<Node<uint8_t>>> &G, Vector<double> &center,
                               const Vector<uint32_t> &in_degree,
                               const Vector<uint32_t> &power) : RunnerBase(G, center, in_degree, power) {
        for (auto &item : bucket) {
            item.reserve(std::min(G.size(), PRE_SERVE_SIZE));
        }
    }

    std::vector<uint32_t> bucket[BUCKET_SIZE];

    void operator()(uint32_t s) {
        uint32_t least = 0;
        bucket[least].push_back(s);
        dist[s] = 0;
        count[s] = 1;
        order.clear();
        for (uint32_t size = 1; size != 0;) {
            for (const uint32_t node : bucket[least % BUCKET_SIZE]) {
                if (least != dist[node])
                    continue;
                order.push_back(node);
                for (const auto &edge : G[node]) {
                    if (least + edge.cost < dist[edge.to]) {
                        dist[edge.to] = least + edge.cost;
                        count[edge.to] = count[node];
                        prev[edge.to].clear();
                        prev[edge.to].push_back(node);
                        bucket[dist[edge.to] % BUCKET_SIZE].push_back(edge.to);
                        size++;
                    } else if (least + edge.cost == dist[edge.to]) {
                        count[edge.to] += count[node];
                        prev[edge.to].push_back(node);
                    }
                }
            }
            size -= bucket[least % BUCKET_SIZE].size();
            bucket[least++ % BUCKET_SIZE].clear();
        }
        calculate(s);
    }
};

template <class Runner, class Cost>
void solve(const Vector<InputEdge>& edges, const Vector<uint32_t> &nodes, const Vector<uint32_t> &thorns,
           const Vector<uint32_t> &in_degree, const Vector<uint32_t> &out_degree, const Vector<uint32_t> &power) {
    const uint32_t n = nodes.size();
    Vector<Vector<Node<Cost>>> G(n);
    for (uint32_t i = 0; i < n; i++) {
        G[i].reserve(out_degree[i]);
    }
    for (const auto& edge : edges) {
        G[edge.from].push_back({ edge.to, (Cost)(edge.cost) });
    }
    Vector<double> center[THREAD_SIZE];
    for (auto &item : center) {
        item.assign(n, 0);
    }
    Vector<Runner> runner;
    runner.reserve(THREAD_SIZE);
    for (uint32_t i = 0; i < THREAD_SIZE; i++) {
        runner.emplace_back(G, center[i], in_degree, power);
    }
    std::atomic_int p(0);
    auto get_job = [&]() {
        return std::atomic_fetch_add_explicit(&p, 1, std::memory_order_relaxed);
    };
    auto run = [&](int index) {
        for (int x; (x = get_job()) < n; runner[index](x));
    };
    std::thread threads[THREAD_SIZE];
    for (uint32_t i = 0; i < THREAD_SIZE; i++)
        threads[i] = std::thread(run, i);
    for (auto &thread : threads)
        thread.join();

    Vector<double> centrality(n);
    for (uint32_t i = 0; i < n; i++) {
        for (uint32_t j = 0; j < THREAD_SIZE; j++) {
            centrality[i] += center[j][i];
        }
    }
    Vector<uint32_t> sorted(n);
    std::iota(sorted.begin(), sorted.end(), 0);
    uint32_t top_n = std::min(TOP_N, n);

    std::nth_element(sorted.begin(), sorted.begin() + top_n, sorted.end(), [&](uint32_t left, uint32_t right) {
        if (fabs(centrality[left] - centrality[right]) < eps) return left < right;
        else return centrality[left] > centrality[right];
    });
    std::sort(sorted.begin(), sorted.begin() + top_n, [&](uint32_t left, uint32_t right) {
        if (fabs(centrality[left] - centrality[right]) < eps) return left < right;
        else return centrality[left] > centrality[right];
    });
    auto file = fopen(OUTPUT, "w");
    for (uint32_t i = 0; i < top_n; i++) {
        __builtin_fprintf(file, "%u,%0.3lf\n", nodes[sorted[i]], centrality[sorted[i]]);
    }
    uint32_t left_n = std::min(thorns.size(), TOP_N - top_n);
    for (uint32_t i = 0; i < left_n; i++) {
        __builtin_fprintf(file, "%u,0.000\n", thorns[i]);
    }
    fclose(file);
}

int main() {
    Vector<InputEdge> edges;
    edges.reserve(EDGE_SIZE);
    std::map<uint32_t, std::pair<uint32_t, uint32_t>> degree;
    while (reader.has_next()) {
        uint32_t u = reader.next_int();
        uint32_t v = reader.next_int();
        uint32_t w = reader.next_int();
        if (w == 0) continue;
        edges.push_back({ u, v, w });
        degree[u].first++;
        degree[v].second++;
    }
    reader.close();
    Vector<uint32_t> nodes;
    Vector<uint32_t> thorns;
    nodes.reserve(NODE_SIZE);
    thorns.reserve(NODE_SIZE);
    for (const auto& [key, value] : degree) {
        static const auto thorn = std::make_pair(1u, 0u);
        (value == thorn ? thorns : nodes).push_back(key);
    }
    uint32_t n = nodes.size();
    auto get_index = [&](uint32_t x) {
        auto it = std::lower_bound(nodes.begin(), nodes.end(), x);
        return (uint32_t)(it - nodes.begin());
    };
    auto new_end = edges.begin();
    Vector<uint32_t> power(n, 1);
    for (uint32_t i = 0; i < edges.size(); ++i) {
        uint32_t u = get_index(edges[i].from);
        uint32_t v = get_index(edges[i].to);
        if (u == nodes.size() || nodes[u] != edges[i].from) {
            power[v]++;
            continue;
        }
        *new_end++ = {u, v, edges[i].cost};
    }
    edges.erase(new_end, edges.end());

    Vector<uint32_t> in_degree(n);
    Vector<uint32_t> out_degree(n);
    uint32_t maximum = 0;
    for (auto& edge: edges) {
        maximum = std::max(maximum, edge.cost);
        out_degree[edge.from]++;
        in_degree[edge.to]++;
    }
    if (256 <= maximum)
        solve<RadixHeapImpl, uint32_t>(edges, nodes, thorns, in_degree, out_degree, power);
    else if (maximum < 64)
        solve<CircularQueueImpl<64>, uint8_t>(edges, nodes, thorns, in_degree, out_degree, power);
    else if (maximum < 128)
        solve<CircularQueueImpl<128>, uint8_t>(edges, nodes, thorns, in_degree, out_degree, power);
    else
        solve<CircularQueueImpl<256>, uint8_t>(edges, nodes, thorns, in_degree, out_degree, power);
    return 0;
}
