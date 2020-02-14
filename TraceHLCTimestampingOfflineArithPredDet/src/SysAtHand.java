class SysAtHand
{
    int epsilon;
    int number_of_processes;
    int interval_length;
    int getInterval_length(){return interval_length;}
    void setInterval_length(int interval_length) {this.interval_length = interval_length;}
    void SetEpsilon(int eps){epsilon=eps;}
    void SetNumberOfProcesses(int nproc){number_of_processes=nproc;}
    int GetEpsilon(){return epsilon;}
    int GetNumberOfProcesses(){return number_of_processes;}
}