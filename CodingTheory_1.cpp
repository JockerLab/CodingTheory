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

using namespace std;

int n, k;
vector<vector<int>> g;
vector<vector<pair<int, int>>> lattice;
vector<int> layers;
const double eps = 1e-9;
const double double_min = -numeric_limits<double>::max();

/*
	Производим упорядочивание строк с позиции pos, обновляем границы активных элементов.
*/
inline vector<pair<int, int>> swap_lines(vector<vector<int>>& msf, int pos, vector<pair<int, int>>& ends, bool do_init = false) {
	for (int i = pos; i < k; i++) {
		/*
			Вычисляем исходные позиции начала и конца строк.
		*/
		if (do_init) {
			ends[i] = make_pair(n, 0);

			for (int j = 0; j < n; j++) {
				if (msf[i][j]) {
					if (ends[i].first == n) {
						ends[i].first = j;
					}
					ends[i].second = j;
				}
			}
		}
		/*
			Идем до позиции pos, меняя местами строки так, чтобы
			они были упорядочены по возрастанию позиции начала.
		*/
		for (int j = i; j > pos; j--) {
			if (ends[j].first < ends[j - 1].first) {
				swap(msf[j], msf[j - 1]);
				swap(ends[j], ends[j - 1]);
			}
		}
	}

	return ends;
}

/*
	Приведение порождающей матрицы к минимальной спэновой форме.
*/
inline vector<pair<int, int>> make_msf(vector<vector<int>>& msf) {
	vector<pair<int, int>> ends(k);

	/*
		Изначально упорядочиваем строки по возрастанию начала строк и 
		запоминаем границы активных элементов.
	*/
	swap_lines(msf, 0, ends, true);

	/*
		Если строки имеют одинаковые индексы начала, то к строке с 
		большим номером прибавляем другую по модулю 2 и обновляем границы.
		После каждой итерации делаем упорядочивание оставшихся строк.
	*/
	for (int i = 0; i < k; i++) {
		for (int j = i + 1; j < k; j++) {
			if (ends[j].first == ends[i].first) {
				bool is_first = true;
				for (int z = 0; z < n; z++) {
					msf[j][z] ^= msf[i][z];
					if (msf[j][z]) {
						if (is_first) {
							ends[j].first = z;
							is_first = false;
						}
						ends[j].second = z;
					}
				}
			}
		}

		ends = swap_lines(msf, i + 1, ends);
	}

	/*
		Идем в обратном порядке, обновляя концы строк.
		Если строка с меньшим номером имеет единицу в индексе конца строки с большим номером,
		то прибавляем к первой строке вторую по модулю 2, обновляя границы.
	*/
	for (int i = k - 1; i > 0; i--) {
		for (int j = i - 1; j >= 0; j--) {
			if (msf[j][ends[i].second]) {
				ends[j] = make_pair(n, 0);
				for (int z = 0; z < n; z++) {
					msf[j][z] ^= msf[i][z];
					if (msf[j][z]) {
						if (ends[j].first == n) {
							ends[j].first = z;
						}
						ends[j].second = z;
					}
				}
			}
		}
	}

	/*
		Возвращаем для каждой строки границы её начала и конца.
	*/
	return ends;
}

/*
	Построение решетки
*/
inline void make_lattice() {
	vector<vector<int>> msf = g;
	layers.resize(n + 1);
	/*
		Приводим порождающую матрицу к минимальной спэновой форме.
		И получаем для каждой строки её границы.
	*/
	vector<pair<int, int>> ends = make_msf(msf);
	/*
		last_layer - номера узлов на последнем ярусе.
		last_active - номера активных строк на предыдущем ярусе.
	*/
	vector<int> last_layer, last_active;

	/*
		lattice - решетка, в котором храним ребра.
		layers - количество узлов в решетке для каждого яруса.
		Изначально инициализируем все одним начальным узлом.
	*/
	lattice.emplace_back();
	last_layer.push_back(0);
	layers[0] = layers[n] = 1;

	for (int i = 0; i < n; i++) {
		vector<int> new_active;
		/*
			Вычисляем активные строки на текущем ярусе.
		*/
		for (int j = 0; j < k; j++) {
			if (ends[j].first <= i && i < ends[j].second) {
				new_active.push_back(j);
			}
		}
		/*
			Для нового яруса количество узлов будет равно 2^new_active.size().
			Создаем new_layer для номеров узлов на текущем ярусе.
			Дополнительно запоминаем количество узлов на текущем ярусе.
		*/
		vector<int> new_layer((1 << new_active.size()));
		layers[i + 1] = (1 << new_active.size());
		/*
			Заполняем new_layer и lattice новыми узлами с текущего яруса.
		*/
		for (int j = 0; j < (1 << new_active.size()); j++) {
			new_layer[j] = lattice.size();
			lattice.emplace_back();
		}
		/*
			ids - позиции текущих активных строк в массиве last_active.
			Если строка не была ранее активной, а на текущем яруса стала, то для неё
			значение будет -1.
		*/
		vector<int> ids(new_active.size());
		for (int j = 0; j < new_active.size(); j++) {
			ids[j] = find(last_active.begin(), last_active.end(), new_active[j]) - last_active.begin();
			if (ids[j] == last_active.size()) {
				ids[j] = -1;
			}
		}
		/*
			Проводим ребра между узлами предыдущего яруса и текущего.
		*/
		for (int j = 0; j < last_layer.size(); j++) {
			/*
				is_new = true, если на текущем слое какая-либо строка стала активной,
				false - иначе.
				val - с какого узла на предыдущем ярусе проводим ребра.
				from_to - для каждого узла на предыдущем ярусе пара из номера активной строки
				на предыдущем ярусе и его значением для узла.
			*/
			bool is_new = false;
			int val = 0;
			vector<pair<int, int>> from_to(last_active.size());
			/*
				Заполняем from_to для кажого узла с предыдущего слоя.
			*/
			for (int z = 0; z < last_active.size(); z++) {
				from_to[z] = make_pair(last_active[z], ((j >> z) % 2));
			}
			/*
				С помощью ids выясняем, стала ли строка активной на текущем ярусе и
				считаем номер узла на текущем ярусе, учитывая сохранные значения с
				предыдущего яруса.
			*/
			for (int z = new_active.size() - 1; z >= 0; z--) {
				if (ids[z] == -1) {
					is_new = true;
				}
				else {
					val = val * 2 + ((j >> ids[z]) % 2);
				}
			}
			sort(from_to.begin(), from_to.end());
			/*
				Для случая, когда какая-либо строка становится активной,
				значит для нее надо построить 2 новых ребра, со значением новой строки
				равным 0 и 1.
			*/
			if (is_new) {
				int edge = 0;
				/*
					Добавляем значение 0 для новой активной строки.
				*/
				from_to.push_back(make_pair(new_active[new_active.size() - 1], 0));
				/*
					Вычисляем значение на ребре как произведение столбца МСФ из активных строк
					и соответсвующих перенесенных значений.
				*/
				for (int z = 0; z < from_to.size(); z++) {
					edge ^= from_to[z].second * msf[from_to[z].first][i];
				}
				/*
					Добавляем ребро с посчитанным значением между соответсвующими узлами.
				*/
				lattice[last_layer[j]].push_back(make_pair(new_layer[val], edge));
				/*
					Аналогично, как для 0, только значение новой активной строки приравниваем 1.
				*/
				from_to[from_to.size() - 1].second = 1;
				edge = 0;
				for (int z = 0; z < from_to.size(); z++) {
					edge ^= from_to[z].second * msf[from_to[z].first][i];
				}
				lattice[last_layer[j]].push_back(make_pair(new_layer[val + (1 << (new_active.size() - 1))], edge));
			}
			/*
				Аналогично добавлению ребер для случая, когда появилась новая активная строка.
				Только не рассматриваем 2 случая добавления для новой активной строки, а переносим старые значения.
			*/
			else {
				int edge = 0;
				for (int z = 0; z < from_to.size(); z++) {
					edge ^= from_to[z].second * msf[from_to[z].first][i];
				}
				lattice[last_layer[j]].push_back(make_pair(new_layer[val], edge));
			}
		}

		last_layer = new_layer;
		last_active = new_active;
	}

	/*
		Выводим количество узлов в решетке на каждом ярусе.
	*/
	for (int i = 0; i <= n; i++) {
		cout << layers[i] << ' ';
	}
	cout << '\n';
}

/*
	Кодирование заданного вектора.
*/
inline vector<int> encode(vector<int>& arr) {
	/*
		Перемножаем данный вектор с порождающей матрицей.
	*/
	vector<int> result(n);
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < k; j++) {
			result[i] ^= arr[j] & g[j][i];
		}
	}
	return result;
}

/*
	Декодирование заданного вектора.
*/
inline vector<int> decode(vector<double>& arr) {
	/*
		Считаем максимально возможное значение скалярного произведение данного вектора 
		и вектора, который необходимо получить.
	*/
	vector<pair<pair<double, int>, int>> dp(lattice.size(), make_pair(make_pair(double_min, 0), 0));
	dp[0] = make_pair(make_pair(0, 0), -1);
	int layer = 0, sum = 1;
	/*
		Для каждой вершины из решетки считаем максимум суммы произведения компоненты вектора
		на значения ребра решетки с учетом модуляции.
	*/
	for (int i = 0; i < lattice.size() - 1; i++) {
		if (i >= sum) {
			layer++;
			sum += layers[layer];
		}
		for (int j = 0; j < lattice[i].size(); j++) {
			if (lattice[i][j].second == 0 && dp[i].first.first + arr[layer] - dp[lattice[i][j].first].first.first > eps) {
				dp[lattice[i][j].first].first.first = dp[i].first.first + arr[layer];
				dp[lattice[i][j].first].first.second = 0;
				dp[lattice[i][j].first].second = i;
			}
			if (lattice[i][j].second == 1 && dp[i].first.first - arr[layer] - dp[lattice[i][j].first].first.first > eps) {
				dp[lattice[i][j].first].first.first = dp[i].first.first - arr[layer];
				dp[lattice[i][j].first].first.second = 1;
				dp[lattice[i][j].first].second = i;
			}
		}
	}
	
	/*
		Восстанавливаем вектор, который дает максимальное правдоподобие.
		И возвращаем его.
	*/
	int p = lattice.size() - 1, i = n - 1;
	vector<int> code(n);
	while (p != 0) {
		code[i] = dp[p].first.second;
		i--;
		p = dp[p].second;
	}
	return code;
}

/*
	Моделирование процесса.
*/
inline void simulate(int stn, int iterates, int errors) {
	int count_error = 0, count_iters = iterates;
	random_device rd;
	mt19937 gen(rd());
	uniform_int_distribution<int> distrib(0, 1);
	/*
		Считаем дисперсию.
	*/
	double dispersion = 0.5 * (double)n / (double)k * pow(10, (double)-stn / 10.);
	normal_distribution<> d{ 0, sqrt(dispersion) };
	vector<int> to_encode(k), result_encode, result_decode;
	vector<double> to_decode(n);
	for (int i = 0; i < iterates; i++) {
		/*
			Для каждой итерации генерируем случайный вектор.
		*/
		for (int j = 0; j < k; j++) {
			to_encode[j] = distrib(gen);
		}
		/*
			Кодируем случайный вектор.
		*/
		result_encode = encode(to_encode);
		/*
			Добавляем шум и производим модуляцию.
		*/
		for (int j = 0; j < n; j++) {
			to_decode[j] = (1.0 - 2.0 * result_encode[j]) + d(gen);
		}
		/*
			Декодируем вектор.
		*/
		result_decode = decode(to_decode);
		bool is_correct = true;
		/*
			Считаем, есть ли ошибка.
		*/
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
	/*
		Выводим частоту ошибок.
	*/
	cout << (double)count_error / (double)count_iters << '\n';
}

int main()
{
	freopen("input.txt", "r", stdin);
	freopen("output.txt", "w", stdout);

	string s;

	cin >> n >> k;

	g.resize(k);
	for (int i = 0; i < k; i++) {
		g[i].resize(n);
		for (int j = 0; j < n; j++) {
			cin >> g[i][j];
		}
	}

	/*
		Построение решетки. И вывод количества узлов на каждом ярусе.
	*/
	make_lattice();

	/*
		Считывание, обработка запросов и вывод результатов.
	*/
	while (cin >> s) {
		if (s == "Encode") {
			vector<int> arr(k);

			for (int i = 0; i < k; i++) {
				cin >> arr[i];
			}

			vector<int> result = encode(arr);

			for (int i = 0; i < result.size(); i++) {
				cout << result[i] << ' ';
			}
			cout << '\n';
		}
		else if (s == "Decode") {
			vector<double> arr(n);

			for (int i = 0; i < n; i++) {
				cin >> arr[i];
			}

			vector<int> result = decode(arr);

			for (int i = 0; i < result.size(); i++) {
				cout << result[i] << ' ';
			}
			cout << '\n';
		}
		else if (s == "Simulate") {
			int iterates, errors, stn;

			cin >> stn >> iterates >> errors;

			simulate(stn, iterates, errors);
		}
	}
}
