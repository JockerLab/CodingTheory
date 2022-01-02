#include <vector>
#include <unordered_map>
#include <cstdio>
#include <iostream>
#include <cmath>
#include <algorithm>
#include <string>
#include <time.h>
#include <random>
#include <iterator>
#include <limits>
#include <set>
#include <bitset>

using namespace std;

const double eps = 1e-9;

int n, p, d, k, m, m_2;
vector<int> degree_vector, vector_degree;
bitset<256> g;

// Остаток от деления битовых векторов
inline bitset<256> bit_mod(const bitset<256>& x1, const bitset<256>& mod) {
	bitset<256> x = x1;
	int max_x = 0, max_mod = 0;
	// Поиск последней единицы вектора x
	for (int i = 0; i < x.size(); i++) {
		if (x[i]) {
			max_x = i;
		}
	}
	// Поиск последней единицы вектора mod
	for (int i = 0; i < mod.size(); i++) {
		if (mod[i]) {
			max_mod = i;
		}
	}
	int i = max_x;
	// Пока максимальная степень вектора x не меньше mod, 
	// произодим битовое сложение с вектором mod сдвинутым на diff, чтобы
	// максимальные степени были одинаковы.
	while (i >= max_mod) {
		int diff = i - max_mod;
		if (x[i]) {
			x ^= (mod << diff);
		}
		i--;
	}

	return x;
}

// Остаток от деления битовых векторов
inline int bit_mod(int x, int mod) {
	int max_x = 0, max_mod = 0;
	// Поиск последней единицы вектора x
	for (int i = 0; (1 << i) <= x; i++) {
		if (x & (1 << i)) {
			max_x = i;
		}
	}
	// Поиск последней единицы вектора mod
	for (int i = 0; (1 << i) <= mod; i++) {
		if (mod & (1 << i)) {
			max_mod = i;
		}
	}
	int i = max_x;
	// Пока максимальная степень вектора x не меньше mod, 
	// произодим битовое сложение с вектором mod сдвинутым на diff, чтобы
	// максимальные степени были одинаковы.
	while (i >= max_mod) {
		int diff = i - max_mod;
		if (x & (1 << i)) {
			x ^= (mod << diff);
		}
		i--;
	}

	return x;
}

// Умножение битовых векторов
inline bitset<256> bit_mul(const bitset<256>& a, const bitset<256>& b) {
	bitset<256> result;
	int a_last = -1, b_last = -1;
	// Поиск последней единицы вектора a
	for (int i = a.size() - 1; i >= 0; i--) {
		if (a[i]) {
			a_last = i;
			break;
		}
	}
	// Умножение каждой ненулевой степени вектора a на битовый вектор b
	for (int i = 0; i <= a_last; i++) {
		if (a[i]) {
			result ^= (b << i);
		}
	}
	return result; 
}

// Умножение битовых векторов
inline int bit_mul(int a, int b) {
	if (!a || !b) {
		return 0;
	}
	// Поиск степеней в поле для векторов a и b
	int degree_a = vector_degree[a],
		degree_b = vector_degree[b];
	// Умножение векторов через сложение степеней
	return degree_vector[(degree_a + degree_b) % n];
}

// Сложение битовых векторов
inline bitset<256> bit_sum(bitset<256>& a, bitset<256>& b) {
	return a ^ b;
}

// Сложение битовых векторов
inline int bit_sum(int a, int b) {
	return a ^ b;
}

// Умножение многочленов над полем GF(2^m)
inline vector<int> poly_mul(const vector<int>& a, const vector<int>& b) {
	vector<int> result(a.size() + b.size() - 1);
	// Перемножаем два многочлена a и b, перебирая и перемножая все пары элементов
	for (int i = 0; i < a.size(); i++) {
		for (int j = 0; j < b.size(); j++) {
			result[i + j] = bit_sum(result[i + j], bit_mul(a[i], b[j]));
		}
	}
	return result;
}

// Построение отображения из степени α в бинарный вектор по модулю примитивного многочлена
inline void make_field() {
	degree_vector.resize(n + 1);
	vector_degree.resize(n + 1);
	degree_vector[0] = 1;
	vector_degree[0] = -1;
	vector_degree[1] = 0;
	// Для каждой степени строим данное отображение
	for (int i = 1; i < n; i++) {
		int cur = bit_mod(degree_vector[i - 1] << 1, p);
		degree_vector[i] = cur;
		vector_degree[cur] = i;
	}
}

// Поиск порождающего многочлена 
inline void find_generative_poly() {
	set<vector<int>> polys;
	// Находим минимальный многочлен для каждой степени α от 1 до d - 1
	for (int i = 1; i < d; i++) {
		set<int> elems;
		int degree = i;
		elems.insert(degree);
		// Для каждой степени возводим ее в квадрат до тех пор, пока не встретим повторяющиеся элементы
		while (degree) {
			degree <<= 1;
			degree = vector_degree[bit_mod(degree_vector[degree % n], p)];
			if (elems.count(degree)) {
				break;
			}
			elems.insert(degree);
		}
		vector<int> result;
		// Строим минимальный многочлен, перемножая многочлены состоящие из эелементов, степени, которых получились ранее и 1.
		for (int elem : elems) {
			vector<int> poly(2);
			poly[0] = degree_vector[elem];
			poly[1] = 1;
			if (!result.size()) {
				result = poly;
			}
			else {
				result = poly_mul(result, poly);
			}
		}
		polys.insert(result);
	}
	// Перемножаем различные минимальные многочлены.
	vector<int> g_res;
	for (vector<int> poly : polys) {
		if (!g_res.size()) {
			g_res = poly;
		}
		else {
			g_res = poly_mul(g_res, poly);
		}
	}
	// Вычиляем размерность кода.
	k = n - g_res.size() + 1;
	for (int i = 0; i < g_res.size(); i++) {
		g[i] = g_res[i];
	}
}

// Кодирование
inline bitset<256> encode(const bitset<256>& arr) {
	bitset<256> a, result;
	a[n - k] = 1;
	// Умножение кодируемого вектора на x^(n - k)
	a = bit_mul(a, arr);
	// Остаток от деления на порождающий многочлен
	result = bit_mod(a, g);
	// Суммируем два слагаемых
	result = bit_sum(result, a);
	return result;
}

// Поиск синдрома вектора
inline vector<int> find_syndrome(bitset<256>& arr) {
	vector<int> s(d - 1, -1);
	int last_a = 0;
	// Поиск последней единицы вектора
	for (int i = 0; i < arr.size(); i++) {
		if (arr[i]) {
			last_a = i;
		}
	}
	// Для каждой степени α от 1 до d-1 подставим их в вектор
	for (int j = 1; j <= d - 1; j++) {
		int bit_a = 1, sum = 0;
		if (s[j - 1] == -1) {
			// Подставляем значния степени в многочлен
			for (int i = 0; i <= last_a; i++) {
				if (arr[i]) {
					sum = bit_sum(sum, bit_a);
				}
				bit_a = bit_mul(bit_a, degree_vector[j]);
			}
			// Используя, y(a^2) = y(a)^2 посчитаем сразу значения для 
			// следующих степеней, умножая их на 2. 
			s[j - 1] = sum;
			int cur_mul = sum;
			for (int i = j * 2; i <= d - 1; i *= 2) {
				cur_mul = bit_mul(cur_mul, cur_mul);
				s[i - 1] = cur_mul;
			}
		}
	}
	return s;
}

// Алгоритм Берлекампа-Месси
inline vector<int> berlekamp_massey(vector<int>& s) {
	// Инициализируем значения
	vector<int> a(d - 1), b(d - 1);
	int r = 1, _m = 0, L = 0;
	a[0] = 1;
	b[0] = 1;
	while (r <= d - 1) {
		int delta = 0;
		// Вичисляем значение delta
		for (int i = 0; i <= L; i++) {
			delta = bit_sum(delta, bit_mul(a[i], s[r - 1 - i]));
		}
		if (delta != 0) {
			vector<int> T = a;
			// Вычисляем вектор T.
			for (int i = r - _m, j = 0; i < d - 1; i++, j++) {
				T[i] = bit_sum(T[i], bit_mul(b[j], delta));
			}
			if (2 * L <= r - 1) {
				int delta1 = degree_vector[(n - vector_degree[delta]) % n];
				// Вычисляем вектор b.
				for (int i = 0; i < d - 1; i++) {
					b[i] = bit_mul(a[i], delta1);
				}
				a = T;
				L = r - L;
				_m = r;
			}
			else {
				a = T;
			}
		}
		r++;
	}
	return a;
}

// Поиск корней многочлена локаторов ошибок
inline void find_roots(bitset<256>& arr, vector<int>& a) {
	int last_a = 0;
	// Поиск последней единицы вектора a
	for (int i = 0; i < a.size(); i++) {
		if (a[i]) {
			last_a = i;
		}
	}
	// Для каждого числа от 1 до n подставляем в многочлен локаторов ошибок,
	// если число оказалось корнем, значит меняем соответсвующее значение декодируемого вектора.
	for (int x = 1; x <= n; x++) {
		int sum = 0, x1 = 1;
		for (int i = 0; i <= last_a; i++) {
			sum = bit_sum(sum, bit_mul(a[i], x1));
			x1 = bit_mul(x1, x);
		}
		if (sum == 0) {
			int err = vector_degree[x];
			arr.flip((n - err) % n);
		}
	}
}

// Декодирование
inline bitset<256> decode(bitset<256>& arr) {
	// Поиск синдрома вектора
	vector<int> s = find_syndrome(arr);
	// Алгоритм Берлекампа-Месси
	vector<int> a = berlekamp_massey(s);
	// Поиск корней многочлена локаторов ошибок
	find_roots(arr, a);
	return arr;
}

// Моделирование процесса
inline void simulate(double stn, int iterates, int errors) {
	int count_error = 0, count_iters = iterates;
	random_device rd;
	mt19937 gen(rd());
	uniform_int_distribution<int> distrib(0, 1);
	uniform_real_distribution<> d(0., 1.);
	bitset<256> to_encode, result_encode, result_decode, to_decode;
	for (int i = 0; i < iterates; i++) {
		// Генерируем вектор для каждой итерации
		for (int j = 0; j < k; j++) {
			to_encode[j] = distrib(gen);
		}
		// Кодируем данный вектор
		result_encode = encode(to_encode);
		to_decode = result_encode;
		// Если вероятность оказалась меньше, чем параметр, то меняем бит
		for (int j = 0; j < n; j++) {
			if (d(gen) <= stn) {
				to_decode.flip(j);
			}
		}
		// Декодируем вектор
		result_decode = decode(to_decode);
		bool is_correct = true;
		// Проверяем на наличие ошибок
		for (int j = 0; j < n; j++) {
			if (result_encode[j] != result_decode[j]) {
				is_correct = false;
			}
		}

		if (!is_correct) {
			count_error++;
		}
		if (count_error >= errors) {
			count_iters = i + 1;
			break;
		}
	}
	// Выводим частоту ошибок
	cout << (double)count_error / (double)count_iters << '\n';
}

int main() {
	freopen("input.txt", "r", stdin);
	freopen("output.txt", "w", stdout);

	string s;

	cin >> n >> p >> d;

	// Построение отображения из степени α в бинарный вектор по модулю примитивного многочлена
	make_field();
	// Поиск порождающего многочлена 
	find_generative_poly();

	// Вывод размерности кода
	cout << k << '\n';
	// Вывод порождающего многочлена
	for (int i = 0; i < n - k + 1; i++) {
		cout << g[i] << ' ';
	}
	cout << '\n';

	while (cin >> s) {
		if (s == "Encode") {
			bitset<256> arr;
			for (int i = 0; i < k; i++) {
				int val;
				cin >> val;
				arr[i] = val;
			}
			bitset<256> result = encode(arr);
			for (int i = 0; i < n; i++) {
				cout << result[i] << ' ';
			}
			cout << '\n';
		}
		if (s == "Decode") {
			bitset<256> arr;
			for (int i = 0; i < n; i++) {
				int val;
				cin >> val;
				arr[i] = val;
			}
			bitset<256> result = decode(arr);
			for (int i = 0; i < n; i++) {
				cout << result[i] << ' ';
			}
			cout << '\n';
		}
		if (s == "Simulate") {
			double stn;
			int iterates, errors;
			cin >> stn >> iterates >> errors;
			simulate(stn, iterates, errors);
		}
	}

	return 0;
}