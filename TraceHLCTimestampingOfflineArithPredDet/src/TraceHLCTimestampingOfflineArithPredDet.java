import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;
import java.util.*;

public class TraceHLCTimestampingOfflineArithPredDet {
    static int snapshotcount=0;
    static int flex_window_snapshotcount=0;
    static int fixed_window_snapshotcount=0;
    static String inpfilename="";
    static int debugmode=0;
    static int mode=0; //msg distribution mode
    static String clockmode="HLC";
    static float gamma = 0;//value by which right end point of the interval will be extended
    static String outputLocation = "";
    public static void main(String[] args)
    {
        try
        {
            if(args.length < 5) {
                System.out.println("Expected number of arguments: 5. Provided "+args.length);
                System.exit(0);
            }
            debugmode = Integer.parseInt(args[0]); //debugmode==1 is printing mode, debugmode == 2 only prints changepoints and candidates
            mode=Integer.parseInt(args[1]); //if 2-different-msg-distr-mode, anything else is normal msg distribution mode..
            /*if(mode==2) {
                System.out.println("Different message distribution mode");
            } else if(mode==1) {
                System.out.println("Intra group message distribution mode");
            } else {
                System.out.println("Normal message distribution mode");
            }*/
            //setting gamma to -1 here by providing -1 as the third input argument - will set it to epsilon below
            gamma = Float.parseFloat(args[2]);
            inpfilename = args[3];
            outputLocation = args[4];
            File inputFile = new File(inpfilename);
            SAXParserFactory factory = SAXParserFactory.newInstance();
            SAXParser saxParser = factory.newSAXParser();//create XML parser instance
            UserHandler userhandler = new UserHandler();
            saxParser.parse(inputFile, userhandler);
            System.out.println("The total snapshot count: "+snapshotcount);
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
}
class UserHandler extends DefaultHandler
{
    boolean bmsender_time = false;
    boolean bmsgto = false;
    boolean bmsgfrom = false;
    boolean bmreceiver_time = false;
    boolean bstart_time=false;
    boolean bend_time=false;
    boolean bmisc=false;
    int proc_id=-1;//variable to remember process id
    int sender_time=-1;// variable to remember sender time for message RECEIVE
    int senderid=-1;// variable to remember sender id for message RECEIVE
    SysAtHand sysathand=new SysAtHand(); //object that accounts for epsilon and number of processes in current system
    Map<Integer, Process> mapofprocesses = new HashMap<Integer, Process>();//map of processes with process id as the key and Process instance as value
    Vector<Double> rcv_probab; //declared but will be defined only if in "different-msg-distr-mode"
    HLC largestIntervalEnd;
    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException
    {
        if (qName.equalsIgnoreCase("message"))
        {
            String type = attributes.getValue("type");
            String process = attributes.getValue("process");
            //System.out.println("message " + type + " event at process " +process);
            proc_id=Integer.parseInt(process);
        }
        else if(qName.equalsIgnoreCase("sys"))
        {
            int eps = Integer.parseInt(attributes.getValue("epsilon"));
            int nproc = Integer.parseInt(attributes.getValue("number_of_processes"));
            //System.out.println("System: epsilon=" + eps + ", number_of_processes=" +nproc);
            sysathand.SetEpsilon(eps);
            sysathand.SetNumberOfProcesses(nproc);

            //setting gamma to epsilon if the provided value is negative
            if(TraceHLCTimestampingOfflineArithPredDet.gamma < 0) {
                TraceHLCTimestampingOfflineArithPredDet.gamma = sysathand.GetEpsilon();
            } else if(TraceHLCTimestampingOfflineArithPredDet.gamma > 0){
                TraceHLCTimestampingOfflineArithPredDet.gamma = (int)Math.floor(sysathand.GetEpsilon() * TraceHLCTimestampingOfflineArithPredDet.gamma);
            }
            else {
                //use 0 as gamma value
            }
            if((TraceHLCTimestampingOfflineArithPredDet.mode==1)||(TraceHLCTimestampingOfflineArithPredDet.mode==2))
            {
                rcv_probab=new Vector<Double>(nproc);
            }
            //create nproc number of instances of class process and assign ids to them
            for (int i=0; i<nproc; i++)
            {
                Clock nwclock=new Clock();
                if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
                {
                    Vector<Integer> hlcvector=new Vector<Integer>();
                    hlcvector.add(0);
                    hlcvector.add(0);
                    hlcvector.add(0);
                    nwclock=new HLC(hlcvector);
                }
                Process proc = new Process(i,nwclock);
                mapofprocesses.put(i,proc);
                if((TraceHLCTimestampingOfflineArithPredDet.mode==1)||(TraceHLCTimestampingOfflineArithPredDet.mode==2)){
                    if(i<nproc/2) {
                        rcv_probab.add(0.5);
                    } else {
                        rcv_probab.add(1.0);
                    }
                }
            }
            //variable to keep track of the largest know HLC timestamp -- needed to bound
            //epsilon extension of last change-points at processes
            Vector<Integer> tempVector = new Vector<Integer>();
            tempVector.add(0);
            tempVector.add(0);
            tempVector.add(0);
            largestIntervalEnd=new HLC(tempVector);
        }
        else if (qName.equalsIgnoreCase("sender_time"))
        {
            bmsender_time = true;
        }
        else if (qName.equalsIgnoreCase("to"))
        {
            bmsgto = true;
        }
        else if (qName.equalsIgnoreCase("from"))
        {
            bmsgfrom = true;
        }
        else if (qName.equalsIgnoreCase("receiver_time"))
        {
            bmreceiver_time = true;
        }
        else if (qName.equalsIgnoreCase("interval"))
        {
            String process = attributes.getValue("process");
            //System.out.println("Interval at process " +process);
            proc_id=Integer.parseInt(process);
        }
        else if (qName.equalsIgnoreCase("start_time"))
        {
            bstart_time = true;
        }
        else if (qName.equalsIgnoreCase("end_time"))
        {
            bend_time = true;
        }
        else if (qName.equalsIgnoreCase("associated_variable"))
        {
            String name = attributes.getValue("name");
            String value = attributes.getValue("value");
            String old_value = attributes.getValue("old_value");
            Process proc= mapofprocesses.get(proc_id);
            //create separate version of clocks for the candidate
            Clock nwclock1=new Clock();
            Clock nwclock2=new Clock();
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
            {
                Vector<Integer> hlcvector1=new Vector<Integer>();
                hlcvector1.add(0);
                hlcvector1.add(0);
                hlcvector1.add(0);
                nwclock1=new HLC(hlcvector1);
                //there is guarantee that the old clock should correspond to
                //interval start because no event happens between intervals,
                //the interval start is either end of a false interval or
                //true interval (due to interval split due to communication),
                //either way this value is recorded as old clock value when
                //"endtime" of current interval got processed
                nwclock1.setClock(proc.getProcOldClock().getClock());
                Vector<Integer> hlcvector2=new Vector<Integer>();
                hlcvector2.add(0);
                hlcvector2.add(0);
                hlcvector2.add(0);
                nwclock2=new HLC(hlcvector2);
                nwclock2.setClock(proc.getProcClock().getClock());
                //keeping track of the actual clock value of the largest interval end
                if(largestIntervalEnd.lessThan(nwclock2)){
                    largestIntervalEnd.setClock(nwclock2.getClock());
                }
                nwclock2.setClockPlusValue((int)TraceHLCTimestampingOfflineArithPredDet.gamma);
                if(value.equals("true"))
                {
                    //this was used for an earlier implementation where intervals were
                    //reported as pairs of end-points and intervals during which the value of the local variable "x"
                    //at a process was true were also referred to as true-intervals were reported as "Candidates"
                    //add candidate to process queue
                    proc.newCandidateOccurance(nwclock1,nwclock2);
                    //add change-points to process queue
                    proc.newChangePoint(nwclock1,1,1);
                    proc.newChangePoint(nwclock2,-1,1);
                }
                /* //uncomment the else part when you have the implementation for processing arithmetic intervals ready
                else{
                    proc.newChangePoint(nwclock1,1,0);
                    proc.newChangePoint(nwclock2,-1,0);
                }
                 */
                mapofprocesses.put(proc_id,proc);
            }
        }
        else if (qName.equalsIgnoreCase("misc"))
        {
            bmisc = true;
        }
    }

    @Override
    public void endElement(String uri, String localName, String qName) throws SAXException
    {
        if (qName.equalsIgnoreCase("message"))
        {
            //System.out.println("End Element :" + qName+ "\n");
        }
        else if(qName.equalsIgnoreCase("associated_variable"))
        {
            //System.out.println("End Element :" + qName);
        }
        else if(qName.equalsIgnoreCase("misc"))
        {
            //System.out.println("End Element :" + qName);
        }
        else if(qName.equalsIgnoreCase("interval"))
        {

        }
        else if(qName.equalsIgnoreCase("system_run"))
        {
            ProcessAndClearCandQueues_HLC();
        }
    }

    @Override
    public void characters(char ch[], int start, int length) throws SAXException
    {
        if (bmsender_time)
        {
            sender_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Sender time: "+ sender_time);
            bmsender_time = false;
        }
        else if (bmsgto)
        {
            int msgto=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Message to: " + msgto);
            Process proc= mapofprocesses.get(proc_id);
            if(proc_id!=msgto)
            {
                proc.updateClockLocalOrSengMsg(sender_time,true);
            }
            else
            {
                proc.updateClockLocalOrSengMsg(sender_time,false);//no reporting required for intra-process communication, so logging corresponding l,c values in the queue is not required
            }
            mapofprocesses.put(proc_id,proc);
            proc_id=-1;
            sender_time=-1;
            //System.out.println("Clock updated after message send, l="+ proc.getL()+",c="+proc.getC());
            bmsgto = false;
        }
        else if (bmsgfrom)
        {
            senderid=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Message from: " +senderid );
            bmsgfrom = false;
        }
        else if (bmreceiver_time)
        {
            int receiver_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Receiver time: " + receiver_time);
            //get max of sendertime,receiver_time
            //update clock using that max
            Process proc= mapofprocesses.get(proc_id);
            boolean toss;
            if((TraceHLCTimestampingOfflineArithPredDet.mode==1) && ((proc_id<5 && senderid>=5)||(proc_id>=5 && senderid<5)))//cross group communication in the case of mode 1
            {
                toss=false;
            }
            else if((TraceHLCTimestampingOfflineArithPredDet.mode==2)|| (TraceHLCTimestampingOfflineArithPredDet.mode==1))// intra group communication in mode 1 OR mode 2
            {
                //System.out.println("rcv_probab at p"+proc_id+" : "+rcv_probab.get(proc_id));
                int rangeend=(int) (1/rcv_probab.get(proc_id)); //2 if probab is 0.5, and 1 otherwise
                toss= new Random().nextInt(rangeend)==0; //
            }
            else
            {
                toss=true; // every process receives every message from any other process
            }
            if((proc_id!=senderid) && (toss))//based on senderid and on receiver-probability--- if in different msg distribution mode			
            {
                //get sender l,c by popping sender's dequeue
                Process senderproc= mapofprocesses.get(senderid);
                MessageSendStruct correspSendClk = senderproc.getClockfromQueue(sender_time);

                proc.updateClockMessageRceive(receiver_time, correspSendClk.getMsgClock());

                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
            }
            else
            {
                if(proc_id!=senderid) // case where it chose to ignore msg based on probability
                {
                    // to pop corresponding sender info from its queue
                    Process senderproc= mapofprocesses.get(senderid);//get sender l,c by popping sender's dequeue
                    MessageSendStruct correspSendLC = senderproc.getClockfromQueue(sender_time);
                }
                proc.updateClockLocalOrSengMsg(receiver_time,false);
                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
            }
            bmreceiver_time = false;
            proc_id=-1;
            sender_time=-1;
            senderid=-1;
        }
        else if (bstart_time)
        {
            //System.out.println("Interval start time: "+ new String(ch, start, length));
            bstart_time = false;
        }
        else if (bend_time)
        {
            int end_time=Integer.parseInt(new String(ch, start, length));
            //System.out.println("Interval end time: " + end_time);
            Process proc= mapofprocesses.get(proc_id);

            //no need to update clocks if bmisc because the clock was already updated at message send/recieve which actually caused this interval end point
            if(!bmisc)
            {
                proc.updateClockLocalOrSengMsg(end_time,false);
                mapofprocesses.put(proc_id,proc);
            }
            bmisc = false;
            bend_time = false;
        }
        else if (bmisc)
        {
            //System.out.println("misc: " + new String(ch, start, length));
        }
    }
    void ProcessAndClearCandQueues_HLC()
    {
        if (sysathand.GetNumberOfProcesses()==0) {
            System.out.println("Zero processes in system.");
            System.exit(0);
        }
        //get the text between last backslash and .xml
        String folderName = TraceHLCTimestampingOfflineArithPredDet.inpfilename.substring(TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf('/')+1, TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf(".xml"));
        String nwfolder=TraceHLCTimestampingOfflineArithPredDet.outputLocation+"\\"+folderName; //input file name without file extension
        //For debugging purposes
        /*****************print all candidates and changepoints of all the processes before preprocessing***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
            String snapshot_cand_file="",snapshot_cpt_file="";
            if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                snapshot_cand_file = nwfolder + "\\before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                snapshot_cpt_file = nwfolder + "\\before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
            } else {
                snapshot_cand_file = nwfolder + "\\before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + "\\before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++){//loop through all process queues
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            currProc.setCPtQueue(currProc.cleanUpChangePtQ());
            currProc.fixLastChangepoint(largestIntervalEnd);
        }
        /*****************print all candidates and changepoints of all the processes to see if change points were processed correctly***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
            String snapshot_cand_file="",snapshot_cpt_file="";
            if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                snapshot_cand_file = nwfolder + "\\candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode +".txt";
                snapshot_cpt_file = nwfolder + "\\changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode +".txt";
            } else {
                snapshot_cand_file = nwfolder + "\\candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + "\\changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        //create variable overlap_count
        int overlap_count= 0;
        int prevtokenend = 0;
        //variable for window based overlap count
        int previous_window=0;
        int minCPtProc=-1;	//process corresponding to the minimum changepoint
        do //until minCPtProc=-1 at the end of the loop - there is no more unprocessed changepoint to process
        {
            /**********Find minimum among first changepoint in each process' queue*******/
            minCPtProc = findMinCptProc();
            //if at least one process had at least one changepoint to process, then minCPtProc is not -1
            if (minCPtProc!=-1)
            {
                //removing the minimum changepoint from the respective queue and processing it
                Process chosenProc= mapofprocesses.get(minCPtProc);//get the current state of the process
                Deque<ChangePoint> chosenProccPtq = chosenProc.getCPtQueue();//get the changepoint queue of the process
                if (chosenProccPtq.isEmpty()) {
                    System.out.println("Something went wrong. Queue at the chosen process is empty.");
                    System.exit(0);
                }
                ChangePoint currentCPt=chosenProccPtq.removeFirst();
                /**************************update overlap count accordingly**************************/
                overlap_count=overlap_count+currentCPt.getEndPointType();
                //remember the effect of clearing the candidate queue of the process
                chosenProc.setCPtQueue(chosenProccPtq);
                //remember to update mapofprocesses accordingly
                mapofprocesses.put(minCPtProc,chosenProc);
                /*************Report timestamp of overlap if it corresponds to a consistent cut****************/
                if (overlap_count==sysathand.GetNumberOfProcesses())
                {
                    String snapshot_outfile="",snapshot_flex_window_counted_outfile="",snapshot_fixed_window_counted_outfile="";
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                        //********************************creating needed files and folders reporting*******************************
                        if(TraceHLCTimestampingOfflineArithPredDet.gamma==0){
                            snapshot_outfile=nwfolder+"\\snapshots_clk_"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                            snapshot_flex_window_counted_outfile=nwfolder+"\\snapshots_flex_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                            snapshot_fixed_window_counted_outfile=nwfolder+"\\snapshots_fixed_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+".txt";
                        } else {
                            snapshot_outfile=nwfolder+"\\snapshots_clk_"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                            snapshot_flex_window_counted_outfile=nwfolder+"\\snapshots_flex_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                            snapshot_fixed_window_counted_outfile=nwfolder+"\\snapshots_fixed_window_counted_clk"+TraceHLCTimestampingOfflineArithPredDet.clockmode+"_gamma"+(int)TraceHLCTimestampingOfflineArithPredDet.gamma+".txt";
                        }
                        //Create folder and files only if it is the first time
                        if(TraceHLCTimestampingOfflineArithPredDet.snapshotcount==0){ //when the first cut gets detected clean the snapshots file if one already exists
                            fileClearCreateParentDirectory(snapshot_outfile);
                            fileClearCreateParentDirectory(snapshot_flex_window_counted_outfile);
                            fileClearCreateParentDirectory(snapshot_fixed_window_counted_outfile);
                        }
                    //}
                    boolean markifcounted=false;
                    /*********************FLEXIBLE WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    prevtokenend = flexWindowCountSnapshot(currentCPt, prevtokenend,minCPtProc,snapshot_flex_window_counted_outfile);
                    /*********************FIXED WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    int temp_window = previous_window;
                    previous_window = fixedWindowCountSnapshot(currentCPt,previous_window,minCPtProc,snapshot_fixed_window_counted_outfile);
                    if (temp_window!=previous_window){
                        markifcounted = true;
                    }
                    /********************writing to all-snapshots file (counted or not)**************************/
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                    reportSnapshot(currentCPt,snapshot_outfile,  minCPtProc, markifcounted);
                    //}
                }//end of if overlap == number of processes
            }//end of if (minCPtProc!=-1)
        }while(minCPtProc!=-1);
        //System.out.println("No more Changepoints to process.");
        System.out.println("Window based snapshot count:"+ TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount);
    }
    int getWindow(int cPtLvalue, int syseps)
    {
        int window=cPtLvalue/syseps;
        //System.out.println("smallestptincut:"+smallestptincut+";syseps:"+syseps+";Window:"+window);
        return window;
    }
    int findMinCptProc(){
        int minCPtProc=-1; //set to default value beginning
        Vector<Integer> temp= new Vector<Integer>();
        temp.add(0);
        temp.add(0);
        temp.add(0);
        //variable for finding and storing minimum changepoint
        ChangePoint minCPt= new ChangePoint(new HLC(temp),0,-1);
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process otherProc= mapofprocesses.get(i); //get the current state of the process
            Deque<ChangePoint> otherProccPtq=otherProc.getCPtQueue();//get the changepoint queue of the process
            if (!otherProccPtq.isEmpty())//if there is at least one unprocessed changepoint
            {
                ChangePoint cPt = otherProccPtq.getFirst();//get current first changepoint in queue
                if (minCPtProc==-1) //default value is -1,
                {
                    minCPt=cPt;	//setting the changepoint from the first process as minimum to start with
                    minCPtProc=i;
                }
                else{
                    int minl=minCPt.getcPointTimestamp().getClock().get(1);
                    int minc=minCPt.getcPointTimestamp().getClock().get(2);
                    int minPtType=minCPt.getEndPointType();
                    int currentl=cPt.getcPointTimestamp().getClock().get(1);
                    int currentc=cPt.getcPointTimestamp().getClock().get(2);
                    int currentPtType=cPt.getEndPointType();
                    //compare l and c values of all the smallest changepoints across processes
                    // if l and c values are equal then right endpoints have higher priority than left endpoints - i.e. they should be processed first
                    if (((currentl== minl)&&(currentc== minc)&&(currentPtType<minPtType)) || ((currentl< minl) || ((currentl== minl)&&(currentc< minc))))
                    {
                        minCPt=cPt;
                        minCPtProc=i;
                    }
                }
            }
        }
        return minCPtProc;
    }
    void printCandidatesForAllProc(String filename){
        fileClearCreateParentDirectory(filename);
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCandQueueToFile(filename);
        }
    }
    void printChangepointsForAllProc(String filename){
        fileClearCreateParentDirectory(filename);
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCPtQueueToFile(filename);
        }
    }
    void fileClearCreateParentDirectory(String filename){
        try{//clear current contents of the file
            File ifilename = new File(filename);
            ifilename.getParentFile().mkdirs();//create necessary parent directory
            new PrintWriter(filename).close();//clear current contents of the file
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
    int flexWindowCountSnapshot(ChangePoint currentCPt, int prevtokenend, int minCPtProc, String filename){
        /********Counting the snapshot only if it is epsilon away from previously detected snapshot********/
        int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        //if current overlap's i.e.changepoints' start-l is epsilon away from the previous overlap's start-l
        if((cPtLvalue-prevtokenend>sysathand.GetEpsilon()) || (TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount==0)){
            TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount++;
            //get/save the overlap's ending pt
            prevtokenend=cPtLvalue;
            /**********writing to snapshot_counted_outfile*******************/
            if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                writeSnapshotToFile(minCPtProc, currentCPt, filename,TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount);
            }
        }
        return prevtokenend;
    }
    int fixedWindowCountSnapshot(ChangePoint currentCPt,int previous_window, int minCPtProc, String filename){
        /***Counting the snapshot only if its current-epsilon-based window is different from the previously detected snapshot********/
        //int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        int cPtvalue = currentCPt.getcPointTimestamp().getClock().get(0);
        //compute the current cut's window based on epsilon
        int current_cut_window=getWindow(cPtvalue,sysathand.GetEpsilon());
        if((TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount==0)||(current_cut_window>previous_window))
        {
            TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount++;
            previous_window=current_cut_window;
            //System.out.println("Counted.");
            //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1)
            {
                /***************writing to snapshot_window_counted_outfile************************/
                writeSnapshotToFile(minCPtProc,currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount);
            }
        }
        return previous_window;
    }
    void reportSnapshot(ChangePoint currentCPt, String filename, int minCPtProc, boolean markifcounted){
        TraceHLCTimestampingOfflineArithPredDet.snapshotcount++;
        writeSnapshotToFile(minCPtProc, currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.snapshotcount);
        if(markifcounted) {
            appendToFile(filename," Was Counted");
        }
    }
    void writeSnapshotToFile(int minCPtProc, ChangePoint currentCPt, String filename, int snapshotCount){
        try {
            BufferedWriter bw2 = new BufferedWriter(new FileWriter(filename, true));//true for append
            bw2.write("\n At Process"+minCPtProc+" Snapshot No:"+snapshotCount+"-->");
            bw2.write("[P"+minCPtProc+":<"+currentCPt.getcPointTimestamp().getClock().get(0)+",<"+currentCPt.getcPointTimestamp().getClock().get(1)+","+currentCPt.getcPointTimestamp().getClock().get(2)+">>");
            bw2.close();
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }
    void appendToFile(String filename, String text){
        try{
            BufferedWriter bw1 = new BufferedWriter(new FileWriter(filename, true));//true for append
            bw1.write(text);
            bw1.close();
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
}